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
From Velus Require Import Environment.
From Velus Require Import Operators.
From Velus Require Import CoindStreams IndexedStreams.
From Velus Require Import CoindIndexed.
From Velus Require Import Clocks.
From Velus Require Import Lustre.StaticEnv.
From Velus Require Import Lustre.LSyntax Lustre.LTyping Lustre.LClocking Lustre.LCausality Lustre.LOrdered.
From Velus Require Import Lustre.LSemantics.

Module Type LCLOCKSEMANTICS
       (Import Ids   : IDS)
       (Import Op    : OPERATORS)
       (Import OpAux : OPERATORS_AUX Ids Op)
       (Import Cks   : CLOCKS        Ids Op OpAux)
       (Import Senv  : STATICENV     Ids Op OpAux Cks)
       (Import Syn   : LSYNTAX Ids Op OpAux Cks Senv)
       (Import Typ   : LTYPING Ids Op OpAux Cks Senv Syn)
       (Import Clo   : LCLOCKING Ids Op OpAux Cks Senv Syn)
       (Import LCA   : LCAUSALITY Ids Op OpAux Cks Senv Syn)
       (Import Lord  : LORDERED Ids Op OpAux Cks Senv Syn)
       (Import CStr  : COINDSTREAMS Ids Op OpAux Cks)
       (Import Sem   : LSEMANTICS Ids Op OpAux Cks Senv Syn Lord CStr).

  Import CStr.
  Module IStr := IndexedStreamsFun Ids Op OpAux Cks.
  Module Import CIStr := CoindIndexedFun Ids Op OpAux Cks CStr IStr.

  Lemma history_tl_same_find : forall H H' vars,
      Forall (fun x => orel (EqSt (A:=svalue)) (Env.find x H) (Env.find x H')) vars ->
      Forall (fun x => orel (EqSt (A:=svalue)) (Env.find x (history_tl H)) (Env.find x (history_tl H'))) vars.
  Proof.
    intros * Hsem.
    eapply Forall_impl; [|eauto]. intros; simpl in *.
    destruct (Env.find a H) eqn:Hfind; inv H0.
    - symmetry in H2.
      apply history_tl_find_Some in Hfind. apply history_tl_find_Some in H2.
      rewrite Hfind, H2. constructor. rewrite H3; reflexivity.
    - symmetry in H1.
      apply history_tl_find_None in Hfind. apply history_tl_find_None in H1.
      rewrite Hfind, H1. constructor.
  Qed.

  Lemma sem_var_same_find : forall H H' vars id vs,
      Forall (fun x => orel (EqSt (A:=svalue)) (Env.find x H') (Env.find x H)) vars ->
      In id vars ->
      sem_var H id vs ->
      sem_var H' id vs.
  Proof.
    intros * Hf Hin Hsem.
    simpl_Forall.
    inv Hsem.
    apply Env.find_1 in H1. rewrite H1 in Hf. inv Hf.
    econstructor. eapply Env.find_2; eauto.
    rewrite H2, H4; reflexivity.
  Qed.

  Import List.

  Lemma sem_clock_same_find : forall H H' vars ck bs bs',
      wc_clock vars ck ->
      Forall (fun x => orel (EqSt (A:=svalue)) (Env.find x H') (Env.find x H)) (map fst vars) ->
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

  (** * Alignment proof *)

  Local Ltac simpl_ndup Hnd :=
    simpl in *;
    try rewrite app_nil_r in Hnd; repeat rewrite map_app.

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
      (forall x ck, HasClock Γ x ck ->
               exists xs, sem_var (fst H) x xs /\ sem_clock (fst H) bs ck (abstract_clock xs))
      /\ (forall x ck, HasClock Γ x ck -> IsLast Γ x ->
                 exists xs, sem_var (snd H) x xs /\ sem_clock (fst H) bs ck (abstract_clock xs)).

    Definition clocked_node H bs (env : static_env) :=
      Env.dom (fst H) (map fst env) /\
      sc_vars env H bs.

    Context {PSyn : block -> Prop}.
    Context {prefs : PS.t}.
    Variable G : @global PSyn prefs.

    Section sem_scope.

      Context {A : Type}.

      Variable sem_exp : Sem.history -> exp -> list (Stream svalue) -> Prop.
      Variable sem_block : Sem.history -> A -> Prop.

      Inductive sem_scope_ck : Sem.history -> Stream bool -> (scope A) -> Prop :=
      | Sscope : forall Hi Hi' Hl Hl' bs locs blks,
          (* Content of the internal history : bottom-up constraints *)
          (forall x vs, sem_var Hi' x vs -> ~InMembers x locs -> sem_var Hi x vs) ->
          Env.dom Hi' (map fst (Env.elements Hi) ++ map fst locs) ->

          (* Content of the last history : top-down constraints *)
          Env.refines (@EqSt _) Hl Hl' ->
          (forall x ty ck cx e0 clx,
              In (x, (ty, ck, cx, Some (e0, clx))) locs ->
              exists vs0 vs1 vs,
                sem_exp (Hi', Hl') e0 [vs0]
                /\ sem_var Hi' x vs1
                /\ fby vs0 vs1 vs
                /\ sem_var Hl' x vs) ->

          sc_vars (senv_of_locs locs) (Hi', Hl') bs ->

          sem_block (Hi', Hl') blks ->
          sem_scope_ck (Hi, Hl) bs (Scope locs blks).
    End sem_scope.

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
          sem_var (fst H) x s ->
          sem_exp_ck H b (Evar x ann) [s]

    | Slast:
      forall H b x s ann,
        sem_var (snd H) x s ->
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
        forall H b x s k es lann ss os,
          Forall2 (sem_exp_ck H b) es ss ->
          sem_var (fst H) x s ->
          Forall2 (fun s' => when k s' s) (concat ss) os ->
          sem_exp_ck H b (Ewhen es x k lann) os

    | Smerge:
        forall H b x tx s es lann vs os,
          sem_var (fst H) x s ->
          Forall2Brs (sem_exp_ck H b) es vs ->
          Forall2 (merge s) vs os ->
          sem_exp_ck H b (Emerge (x, tx) es lann) os

    | ScaseTotal:
        forall H b e s es tys ck vs os,
          sem_exp_ck H b e [s] ->
          Forall2Brs (sem_exp_ck H b) es vs ->
          Forall3 (case s) vs (List.map (fun _ => None) tys) os ->
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
          Forall2 (sem_var (fst H)) xs (concat ss) ->
          sem_equation_ck H b (xs, es)

    with sem_transitions_ck : Sem.history -> Stream bool -> list (exp * (enumtag * bool)) -> (enumtag * bool) -> Stream (synchronous (enumtag * bool)) -> Prop :=
    | Stransdef : forall H bs default stres,
        stres ≡ const_stres bs default ->
        sem_transitions_ck H bs [] default stres
    | Strans : forall H bs e C r trans default vs bs' stres1 stres,
        sem_exp_ck H bs e [vs] ->
        bools_of vs bs' ->
        sem_transitions_ck H bs trans default stres1 ->
        stres ≡ choose_first (const_stres bs' (C, r)) stres1 ->
        sem_transitions_ck H bs ((e, (C, r))::trans) default stres

    with sem_block_ck: Sem.history -> Stream bool -> block -> Prop :=
    | Sbeq:
      forall H b eq,
        sem_equation_ck H b eq ->
        sem_block_ck H b (Beq eq)

    | Sreset:
      forall H b blocks er sr r,
        sem_exp_ck H b er [sr] ->
        bools_of sr r ->
        (forall k, Forall (sem_block_ck (Sem.mask_hist k r H) (maskb k r b)) blocks) ->
        sem_block_ck H b (Breset blocks er)

    | Sswitch:
      forall Hi b ec branches sc,
        sem_exp_ck Hi b ec [sc] ->
        wt_streams [sc] (typeof ec) ->
        Forall (fun blks =>
                  exists Hi', Sem.filter_hist (fst blks) sc Hi Hi'
                         /\ let bi := ffilterb (fst blks) sc b in
                           sem_scope_ck (fun Hi' => sem_exp_ck Hi' bi)
                                        (fun Hi' => Forall (sem_block_ck Hi' bi)) Hi' bi (snd blks)) branches ->
        sem_block_ck Hi b (Bswitch ec branches)

    | Sauto:
      forall H bs ini oth states ck bs' stres0 stres1 stres,
        sem_clock (fst H) bs ck bs' ->
        sem_transitions_ck H bs' (List.map (fun '(e, t) => (e, (t, false))) ini) (oth, false) stres0 ->
        fby stres0 stres1 stres ->
        Forall (fun state =>
                  forall k, exists Hik, Sem.select_hist (fst state) k stres H Hik
                              /\ let bik := fselectb (fst state) k stres bs in
                                sem_scope_ck (fun Hi' => sem_exp_ck Hi' bik)
                                             (fun Hi' blks =>
                                                Forall (sem_block_ck Hi' bik) (fst blks)
                                                /\ sem_transitions_ck Hi' bik (snd blks) (fst state, false) (fselect absent (fst state) k stres stres1)
                                             ) Hik bik (snd state)
               ) states ->
        sem_block_ck H bs (Bauto ck (ini, oth) states)

    | Slocal:
      forall Hi bs scope,
        sem_scope_ck (fun Hi' => sem_exp_ck Hi' bs) (fun Hi' => Forall (sem_block_ck Hi' bs)) Hi bs scope ->
        sem_block_ck Hi bs (Blocal scope)

    with sem_node_ck: ident -> list (Stream svalue) -> list (Stream svalue) -> Prop :=
      Snode:
        forall f ss os n H b,
          find_node f G = Some n ->
          Forall2 (sem_var H) (idents n.(n_in)) ss ->
          Forall2 (sem_var H) (idents n.(n_out)) os ->
          sem_block_ck (H, Env.empty _) b n.(n_block) ->
          b = clocks_of ss ->
          clocked_node (H, Env.empty _) b (senv_of_inout (n.(n_in) ++ n.(n_out))) ->
          sem_node_ck f ss os.

    Hint Constructors sem_exp sem_equation : lcsem.

    (** Custom induction schemes *)

    Section sem_exp_ind2.
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
          sem_var (fst H) x s ->
          P_exp H b (Evar x ann) [s].

      Hypothesis LastCase:
        forall H b x s ann,
          sem_var (snd H) x s ->
          P_exp H b (Elast x ann) [s].

      Hypothesis UnopCase:
        forall H b e op ty s o ann,
          sem_exp_ck H b e [s] ->
          P_exp H b e [s] ->
          typeof e = [ty] ->
          lift1 op ty s o ->
          P_exp H b (Eunop op e ann) [o].

      Hypothesis BinopCase:
        forall H b e1 e2 op ty1 ty2 s1 s2 o ann,
          sem_exp_ck H b e1 [s1] ->
          P_exp H b e1 [s1] ->
          sem_exp_ck H b e2 [s2] ->
          P_exp H b e2 [s2] ->
          typeof e1 = [ty1] ->
          typeof e2 = [ty2] ->
          lift2 op ty1 ty2 s1 s2 o ->
          P_exp H b (Ebinop op e1 e2 ann) [o].

      Hypothesis FbyCase:
        forall H b e0s es anns s0ss sss os,
          Forall2 (sem_exp_ck H b) e0s s0ss ->
          Forall2 (P_exp H b) e0s s0ss ->
          Forall2 (sem_exp_ck H b) es sss ->
          Forall2 (P_exp H b) es sss ->
          Forall3 fby (concat s0ss) (concat sss) os ->
          P_exp H b (Efby e0s es anns) os.

      Hypothesis ArrowCase:
        forall H b e0s es anns s0ss sss os,
          Forall2 (sem_exp_ck H b) e0s s0ss ->
          Forall2 (P_exp H b) e0s s0ss ->
          Forall2 (sem_exp_ck H b) es sss ->
          Forall2 (P_exp H b) es sss ->
          Forall3 arrow (concat s0ss) (concat sss) os ->
          P_exp H b (Earrow e0s es anns) os.

      Hypothesis WhenCase:
        forall H b x s k es lann ss os,
          Forall2 (sem_exp_ck H b) es ss ->
          Forall2 (P_exp H b) es ss ->
          sem_var (fst H) x s ->
          Forall2 (fun s' => when k s' s) (concat ss) os ->
          P_exp H b (Ewhen es x k lann) os.

      Hypothesis MergeCase:
        forall H b x tx s es lann vs os,
          sem_var (fst H) x s ->
          Forall2Brs (sem_exp_ck H b) es vs ->
          Forall2Brs (P_exp H b) es vs ->
          Forall2 (merge s) vs os ->
          P_exp H b (Emerge (x, tx) es lann) os.

      Hypothesis CaseTotalCase:
        forall H b e s es tys ck vs os,
          sem_exp_ck H b e [s] ->
          P_exp H b e [s] ->
          Forall2Brs (sem_exp_ck H b) es vs ->
          Forall2Brs (P_exp H b) es vs ->
          Forall3 (case s) vs (List.map (fun _ => None) tys) os ->
          P_exp H b (Ecase e es None (tys, ck)) os.

      Hypothesis CaseDefaultCase:
        forall H b e s es d lann vs vd os,
          sem_exp_ck H b e [s] ->
          P_exp H b e [s] ->
          wt_streams [s] (typeof e) ->
          Forall2Brs (sem_exp_ck H b) es vs ->
          Forall2Brs (P_exp H b) es vs ->
          Forall2 (sem_exp_ck H b) d vd ->
          Forall2 (P_exp H b) d vd ->
          Forall3 (case s) vs (List.map Some (concat vd)) os ->
          P_exp H b (Ecase e es (Some d) lann) os.

      Hypothesis AppCase:
        forall H b f es er lann ss os sr bs,
          Forall2 (sem_exp_ck H b) es ss ->
          Forall2 (P_exp H b) es ss ->
          Forall2 (fun e r => sem_exp_ck H b e [r]) er sr ->
          Forall2 (fun e r => P_exp H b e [r]) er sr ->
          bools_ofs sr bs ->
          (forall k, sem_node_ck f (List.map (maskv k bs) (concat ss)) (List.map (maskv k bs) os)
                /\ P_node f (List.map (maskv k bs) (concat ss)) (List.map (maskv k bs) os)) ->
          P_exp H b (Eapp f es er lann) os.

      Hypothesis Equation:
        forall H b xs es ss,
          Forall2 (sem_exp_ck H b) es ss ->
          Forall2 (P_exp H b) es ss ->
          Forall2 (sem_var (fst H)) xs (concat ss) ->
          P_equation H b (xs, es).

      Hypothesis BeqCase:
        forall H b eq,
          sem_equation_ck H b eq ->
          P_equation H b eq ->
          P_block H b (Beq eq).

      Hypothesis BresetCase:
        forall H b blocks er sr r,
          sem_exp_ck H b er [sr] ->
          P_exp H b er [sr] ->
          bools_of sr r ->
          (forall k, Forall (sem_block_ck (Sem.mask_hist k r H) (maskb k r b)) blocks /\
                Forall (P_block (Sem.mask_hist k r H) (maskb k r b)) blocks) ->
          P_block H b (Breset blocks er).

      Hypothesis BswitchCase:
        forall Hi b ec branches sc,
          sem_exp_ck Hi b ec [sc] ->
          P_exp Hi b ec [sc] ->
          wt_streams [sc] (typeof ec) ->
          Forall (fun blks => exists Hi', Sem.filter_hist (fst blks) sc Hi Hi'
                                  /\ let bi := ffilterb (fst blks) sc b in
                                    sem_scope_ck (fun Hi' e vs => sem_exp_ck Hi' bi e vs /\ P_exp Hi' bi e vs)
                                                 (fun Hi' blks => Forall (sem_block_ck Hi' bi) blks
                                                               /\ Forall (P_block Hi' bi) blks
                                              ) Hi' bi (snd blks)) branches ->
          P_block Hi b (Bswitch ec branches).

      Hypothesis TransDefCase:
        forall Hi bs default stres,
          stres ≡ const_stres bs default ->
          P_transitions Hi bs [] default stres.

      Hypothesis TransCase:
        forall Hi bs e C r trans default vs bs' stres1 stres,
          sem_exp_ck Hi bs e [vs] ->
          P_exp Hi bs e [vs] ->
          bools_of vs bs' ->
          sem_transitions_ck Hi bs trans default stres1 ->
          P_transitions Hi bs trans default stres1 ->
          stres ≡ choose_first (const_stres bs' (C, r)) stres1 ->
          P_transitions Hi bs ((e, (C, r))::trans) default stres.

      Hypothesis BautoCase:
        forall Hi bs ini oth states ck bs' stres0 stres1 stres,
          sem_clock (fst Hi) bs ck bs' ->
          sem_transitions_ck Hi bs' (List.map (fun '(e, t) => (e, (t, false))) ini) (oth, false) stres0 ->
          P_transitions Hi bs' (List.map (fun '(e, t) => (e, (t, false))) ini) (oth, false) stres0 ->
          fby stres0 stres1 stres ->
          Forall (fun state =>
                    forall k, exists Hik,
                      Sem.select_hist (fst state) k stres Hi Hik
                      /\ let bik := fselectb (fst state) k stres bs in
                        sem_scope_ck (fun Hi' e vs => sem_exp_ck Hi' bik e vs /\ P_exp Hi' bik e vs)
                                     (fun Hi' blks => Forall (sem_block_ck Hi' bik) (fst blks)
                                                   /\ Forall (P_block Hi' bik) (fst blks)
                                                   /\ sem_transitions_ck Hi' bik (snd blks) (fst state, false) (fselect absent (fst state) k stres stres1)
                                                   /\ P_transitions Hi' bik (snd blks) (fst state, false) (fselect absent (fst state) k stres stres1)
                                     ) Hik bik (snd state)
                 ) states ->
          P_block Hi bs (Bauto ck (ini, oth) states).

      Hypothesis BlocalCase:
        forall Hi bs scope,
          sem_scope_ck (fun Hi' e vs => sem_exp_ck Hi' bs e vs /\ P_exp Hi' bs e vs)
                       (fun Hi' blks => Forall (sem_block_ck Hi' bs) blks /\ Forall (P_block Hi' bs) blks)
                       Hi bs scope ->
          P_block Hi bs (Blocal scope).

      Hypothesis Node:
        forall f ss os n H b,
          find_node f G = Some n ->
          Forall2 (sem_var H) (idents n.(n_in)) ss ->
          Forall2 (sem_var H) (idents n.(n_out)) os ->
          sem_block_ck (H, Env.empty _) b n.(n_block) ->
          P_block (H, Env.empty _) b n.(n_block) ->
          b = clocks_of ss ->
          clocked_node (H, Env.empty _) b (senv_of_inout (n.(n_in) ++ n.(n_out))) ->
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
               (Sem: sem_exp_ck H b e ss)
               {struct Sem}
        : P_exp H b e ss
      with sem_equation_ck_ind2
             (H: Sem.history) (b: Stream bool) (e: equation)
             (Sem: sem_equation_ck H b e)
             {struct Sem}
        : P_equation H b e
      with sem_transitions_ind2
             (H: Sem.history) (b: Stream bool) trans default stres
             (Sem: sem_transitions_ck H b trans default stres)
             {struct Sem}
        : P_transitions H b trans default stres
      with sem_block_ck_ind2
             (H: Sem.history) (b: Stream bool) (d: block)
             (Sem: sem_block_ck H b d)
             {struct Sem}
           : P_block H b d
      with sem_node_ck_ind2
             (f: ident) (ss os: list (Stream svalue))
             (Sem: sem_node_ck f ss os)
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
          + eapply BresetCase; eauto.
            intros k. specialize (H3 k). split; eauto. SolveForall.
          + eapply BswitchCase; eauto.
            SolveForall. constructor; auto.
            destruct_conjs. inv H4. do 2 esplit; eauto.
            econstructor; eauto. 2:split; eauto.
            * intros * Hin. eapply H10 in Hin as (?&?&?&?&?&?&?). do 3 esplit; eauto.
              repeat split; eauto.
            * simpl. SolveForall.
          + eapply BautoCase; eauto.
            SolveForall. constructor; auto.
            intros k. specialize (H0 k). destruct_conjs.
            inv H5. destruct_conjs. esplit. split; eauto.
            econstructor; eauto. 2:split; [|split; [|split]]; eauto.
            * intros * Hin. eapply H11 in Hin as (?&?&?&?&?&?&?). do 3 esplit; eauto.
              repeat split; eauto.
            * simpl. SolveForall.
          + eapply BlocalCase; eauto.
            inv H0. econstructor; eauto. 2:split; auto; SolveForall.
            intros. edestruct H4 as (?&?&?&?&?&?&?); eauto.
            do 3 esplit; eauto. repeat split; eauto.
        - inv Sem.
          eapply Node; eauto.
      Qed.

    End sem_exp_ind2.

    Lemma sem_block_defined : forall blk H bs x,
        sem_block_ck H bs blk ->
        Syn.Is_defined_in x blk ->
        Env.In x (fst H).
    Proof.
      induction blk using block_ind2; intros * Hsem Hdef; inv Hsem; inv Hdef.
      - (* equation *)
        inv H4. eapply Forall2_ignore2, Forall_forall in H8 as (?&?&?); eauto using sem_var_In.
      - (* reset *)
        simpl_Exists.
        specialize (H8 0). simpl_Forall.
        eapply H, Env.map_2 in H8; eauto.
      - (* switch *)
        simpl_Exists; simpl_Forall.
        destruct s; inv H2; inv H4.
        simpl_Exists. simpl_Forall.
        eapply H in H17; eauto. inv H17.
        destruct H1. eapply Env.In_refines; eauto.
        eapply sem_var_In, H11; eauto.
        econstructor; eauto. reflexivity.
      - (* automaton *)
        simpl_Exists; simpl_Forall. specialize (H10 0); destruct_conjs.
        destruct s as [?(?&?)]; inv H3; inv H2.
        simpl_Exists. simpl_Forall.
        eapply H in H2; eauto. inv H2.
        destruct H1. eapply Env.In_refines; eauto.
        eapply sem_var_In, H11; eauto.
        econstructor; eauto. reflexivity.
      - (* local *)
        inv H4. inv H2. simpl_Exists; simpl_Forall.
        eapply H in H12; eauto. inv H12.
        eapply sem_var_In, H5; eauto.
        econstructor; eauto. reflexivity.
    Qed.

    Section sem_refines.

      Fact sem_exp_refines : forall b e H H' Hl v,
        Env.refines (@EqSt _) H H' ->
        sem_exp_ck (H, Hl) b e v ->
        sem_exp_ck (H', Hl) b e v.
      Proof with eauto with datatypes.
        induction e using exp_ind2; intros * Href Hsem; inv Hsem;
          econstructor; eauto using sem_var_refines; simpl_Forall; eauto.
        1-3:(eapply Forall2Brs_impl_In; [|eauto]; intros;
             simpl_Exists; simpl_Forall; eauto).
      Qed.

      Fact sem_equation_refines : forall H H' Hl b equ,
          Env.refines (@EqSt _) H H' ->
          sem_equation_ck (H, Hl) b equ ->
          sem_equation_ck (H', Hl) b equ.
      Proof with eauto.
        intros * Href Hsem. inv Hsem.
        apply Seq with (ss:=ss); simpl_Forall;
          eauto using sem_exp_refines, sem_var_refines.
      Qed.

      Fact sc_vars_refines : forall Γ H H' Hl Hl' b,
          Env.refines (@EqSt _) H H' ->
          Env.refines (@EqSt _) Hl Hl' ->
          sc_vars Γ (H, Hl) b ->
          sc_vars Γ (H', Hl') b.
      Proof.
        intros * Href1 Href2 (Hsc1&Hsc2).
        split; intros; simpl.
        - edestruct Hsc1 as (?&?&?); eauto using sem_var_refines, sem_clock_refines.
        - edestruct Hsc2 as (?&?&?); eauto using sem_var_refines, sem_clock_refines.
      Qed.

      Fact sem_transitions_refines : forall H H' Hl b trans default stres,
          Env.refines (@EqSt _) H H' ->
          sem_transitions_ck (H, Hl) b trans default stres ->
          sem_transitions_ck (H', Hl) b trans default stres.
      Proof with eauto.
        induction trans; intros * Href Hsem; inv Hsem;
          econstructor; eauto using sem_exp_refines.
      Qed.

      Lemma sem_scope_refines {A} P_sem : forall locs (blk: A) H H' Hl bs,
          Env.refines (@EqSt _) H H' ->
          sem_scope_ck (fun Hi e => sem_exp_ck Hi bs e) P_sem (H, Hl) bs (Scope locs blk) ->
          (forall H H' Hl,
              Env.refines (@EqSt _) H H' ->
              P_sem (H, Hl) blk ->
              P_sem (H', Hl) blk) ->
          sem_scope_ck (fun Hi e => sem_exp_ck Hi bs e) P_sem (H', Hl) bs (Scope locs blk).
      Proof.
        intros * Href Hsem Hind; inv Hsem.
        assert (Env.refines (@EqSt _) Hi'
                            (Env.restrict (Env.union H' Hi') (map fst (Env.elements H') ++ map fst locs))) as Href'.
        { intros ?? Hfind. exists v. split; try reflexivity.
          apply Env.restrict_find; eauto using Env.union_find3'.
          eapply incl_appl'. eapply Env.refines_elements; eauto.
          eapply Env.dom_use; eauto. esplit; eauto. }
        eapply Sscope with (Hi':=Env.restrict (Env.union H' Hi') (map fst (Env.elements H') ++ map fst locs)); eauto.
        + intros * Hvar Hnin1.
          eapply sem_var_restrict_inv in Hvar as (_&Hvar). inv Hvar.
          eapply Env.union_find4' in H1 as [(Hfind1&Hfind2)|Hfind2].
          * econstructor; eauto.
          * eapply sem_var_refines; eauto. eapply H4; eauto. econstructor; eauto.
        + eapply Env.dom_lb_restrict_dom, Env.union_dom_lb; eauto.
          * eapply Env.dom_dom_lb, Env.dom_elements.
          * eapply Env.dom_lb_incl, Env.dom_dom_lb; eauto. solve_incl_app.
        + intros. edestruct H8 as (?&?&?&?&?&?&?); eauto.
          do 3 esplit. repeat split; eauto using sem_exp_refines, sem_var_refines.
        + eapply sc_vars_refines. 3:eauto. 1,2:eauto; reflexivity.
      Qed.

      Lemma sem_block_refines : forall blk H H' Hl bs,
          Env.refines (@EqSt _) H H' ->
          sem_block_ck (H, Hl) bs blk ->
          sem_block_ck (H', Hl) bs blk.
      Proof.
        induction blk using block_ind2; intros * Href Hsem;
          inv Hsem.
        - (* eq *)
          constructor; eauto using sem_equation_refines.
        - (* reset *)
          econstructor; eauto using sem_exp_refines.
          intros k. specialize (H8 k).
          simpl_Forall.
          eapply H; [|eauto]; eauto using refines_mask.
        - (* switch *)
          econstructor; eauto using sem_exp_refines.
          + simpl_Forall.
            esplit. split; eauto.
            destruct H2 as (Href1&?). split; simpl in *; [|auto].
            intros ?? Hfind. apply Href1 in Hfind as (?&Hfilter&Hfind').
            apply Href in Hfind' as (?&?&?). do 2 esplit; [|eauto].
            now rewrite <-H5.
        - (* automaton *)
          eapply Sauto; eauto using sem_clock_refines, sem_transitions_refines.
          simpl_Forall. specialize (H10 k); destruct_conjs.
          esplit; split; [|eauto].
          destruct H2 as (Href1&?); split; simpl in *; [|auto].
          intros ?? Hfind. apply Href1 in Hfind as (?&Hfilter&Hfind').
          apply Href in Hfind' as (?&?&?). do 2 esplit; [|eauto].
          now rewrite <-H4.
        - (* local *)
          constructor. eapply sem_scope_refines; eauto.
          intros; simpl_Forall; eauto.
      Qed.

      Corollary sem_scope_refines1 : forall locs blk H H' Hl bs,
          Env.refines (@EqSt _) H H' ->
          sem_scope_ck (fun Hi e => sem_exp_ck Hi bs e)
                       (fun Hi => Forall (sem_block_ck Hi bs)) (H, Hl) bs (Scope locs blk) ->
          sem_scope_ck (fun Hi e => sem_exp_ck Hi bs e)
                       (fun Hi => Forall (sem_block_ck Hi bs)) (H', Hl) bs (Scope locs blk).
      Proof.
        intros.
        eapply sem_scope_refines; eauto.
        intros; simpl_Forall; eauto using sem_block_refines.
      Qed.

      Corollary sem_scope_refines2 : forall locs blk def stres H H' Hl bs,
          Env.refines (@EqSt _) H H' ->
          sem_scope_ck (fun Hi e => sem_exp_ck Hi bs e)
                       (fun Hi blks => Forall (sem_block_ck Hi bs) (fst blks)
                                    /\ sem_transitions_ck Hi bs (snd blks) def stres) (H, Hl) bs (Scope locs blk) ->
          sem_scope_ck (fun Hi e => sem_exp_ck Hi bs e)
                       (fun Hi blks => Forall (sem_block_ck Hi bs) (fst blks)
                                    /\ sem_transitions_ck Hi bs (snd blks) def stres) (H', Hl) bs (Scope locs blk).
      Proof.
        intros.
        eapply sem_scope_refines; eauto.
        intros; destruct_conjs.
        split; simpl_Forall; eauto using sem_block_refines, sem_transitions_refines.
      Qed.

    End sem_refines.

    Section sem_restrict.

      Hypothesis HwcG : wc_global G.

      Fact sem_exp_restrict : forall Γ H Hl b e vs,
          wx_exp Γ e ->
          sem_exp_ck (H, Hl) b e vs ->
          sem_exp_ck (Env.restrict H (map fst Γ), Hl) b e vs.
      Proof.
        induction e using exp_ind2; intros vs Hwt Hsem; inv Hwt; inv Hsem;
          econstructor; eauto; simpl_Forall; eauto.
        1-3:(eapply sem_var_restrict; eauto; apply fst_InMembers;
             take (IsVar _ _) and inv it; auto).
        1-3:(eapply Forall2Brs_impl_In; [|eauto]; intros ?? Hin Hse;
             simpl_Exists; simpl_Forall; eauto).
        specialize (H8 _ eq_refl). simpl_Forall; eauto.
      Qed.

      Lemma sem_equation_restrict : forall Γ H Hl b eq,
          wx_equation Γ eq ->
          sem_equation_ck (H, Hl) b eq ->
          sem_equation_ck (Env.restrict H (map fst Γ), Hl) b eq.
      Proof with eauto with datatypes.
        intros ???? [xs es] Hwc Hsem.
        destruct Hwc as (?&?). inv Hsem.
        econstructor. instantiate (1:=ss).
        + simpl_Forall; eauto using sem_exp_restrict.
        + simpl_Forall. inv H1. eapply sem_var_restrict... now rewrite <-fst_InMembers.
      Qed.

      Fact sc_vars_restrict : forall locs Γ H Hl bs,
          incl (map fst locs) (map fst Γ) ->
          Forall (wc_clock (idck Γ)) (map snd (idck locs)) ->
          sc_vars locs (H, Hl) bs ->
          sc_vars locs (Env.restrict H (map fst Γ), Hl) bs.
      Proof.
        intros * Hincl Hwc1 (?&?).
        split; auto; simpl_Forall; intros.
        - edestruct H0 as (?&?&?); eauto.
          esplit; split; eauto.
          + eapply sem_var_restrict; [|eauto].
            eapply Hincl; inv H2; solve_In.
          + eapply sem_clock_restrict; [|eauto].
            apply wc_clock_wx_clock. inv H2.
            eapply Forall_forall in Hwc1; eauto. 2:solve_In. auto.
        - edestruct H1 as (?&?&?); eauto.
          esplit; split; eauto.
          eapply sem_clock_restrict; [|eauto].
          apply wc_clock_wx_clock. inv H2.
          eapply Forall_forall in Hwc1; eauto. 2:solve_In. auto.
      Qed.

      Fact sem_transitions_restrict : forall Γ H Hl b trans default stres,
          Forall (fun '(e, _) => wx_exp Γ e) trans ->
          sem_transitions_ck (H, Hl) b trans default stres ->
          sem_transitions_ck (Env.restrict H (List.map fst Γ), Hl) b trans default stres.
      Proof with eauto.
        induction trans; intros * Hwx Hsem; inv Hwx; inv Hsem;
          econstructor; eauto using sem_exp_restrict.
      Qed.

      Lemma sem_scope_restrict {A} (P_wc: _ -> _ -> Prop) (sem_block : _ -> _ -> Prop) :
        forall Γ Hi Hl bs locs (blks : A),
          wc_env (idck Γ) ->
          wc_scope P_wc G Γ (Scope locs blks) ->
          sem_scope_ck (fun Hi' => sem_exp_ck Hi' bs) sem_block (Hi, Hl) bs (Scope locs blks) ->
          (forall Γ Hi Hl, wc_env (idck Γ) -> P_wc Γ blks -> sem_block (Hi, Hl) blks -> sem_block (Env.restrict Hi (List.map fst Γ), Hl) blks) ->
          sem_scope_ck (fun Hi' => sem_exp_ck Hi' bs) sem_block (Env.restrict Hi (List.map fst Γ), Hl) bs (Scope locs blks).
      Proof.
        intros * Hwenv Hwc Hsem Hind; inv Hwc; inv Hsem.
        eapply Sscope with (Hi':=Env.restrict Hi' (List.map fst (Γ ++ senv_of_locs locs))); eauto.
        - intros * Hsem Hnin.
          eapply sem_var_restrict_inv in Hsem as (Hin&Hsem).
          eapply sem_var_restrict; eauto.
          simpl_app. apply in_app_iff in Hin as [Hin|Hin]; auto.
          setoid_rewrite map_fst_senv_of_locs in Hin.
          exfalso. apply Hnin, fst_InMembers; auto.
        - eapply Env.dom_intro; intros.
          rewrite Env.restrict_In_iff. erewrite Env.dom_use; [|eauto].
          repeat rewrite in_app_iff. repeat rewrite <-fst_InMembers.
          repeat rewrite <-Env.In_Members. rewrite Env.restrict_In_iff.
          repeat rewrite InMembers_app. rewrite InMembers_senv_of_locs. repeat rewrite <-fst_InMembers.
          split; [intros ([|]&[|])|intros [(?&?)|]]; auto.
        - intros * Hin. edestruct H10; eauto. destruct_conjs.
          simpl_Forall.
          do 3 esplit. repeat split; eauto.
          eapply sem_exp_restrict; eauto with lclocking.
          eapply sem_var_restrict; eauto. simpl_app. apply in_or_app. right. solve_In.
        - eapply sc_vars_restrict; eauto. solve_incl_app.
          simpl_Forall; simpl_In; simpl_Forall; auto.
        - eapply Hind; eauto.
          setoid_rewrite map_app. apply wc_env_app; auto.
          simpl_Forall; simpl_In; simpl_Forall. rewrite <-map_app; auto.
      Qed.

      Lemma sem_block_restrict : forall blk Γ H Hl b,
          wc_env (idck Γ) ->
          wc_block G Γ blk ->
          sem_block_ck (H, Hl) b blk ->
          sem_block_ck (Env.restrict H (map fst Γ), Hl) b blk.
      Proof with eauto with lclocking.
        induction blk using block_ind2; intros * Hwenv1 Hwc Hsem; inv Hwc; inv Hsem.
        - (* equation *)
          econstructor.
          eapply sem_equation_restrict...
        - (* reset *)
          econstructor; eauto.
          + eapply sem_exp_restrict...
          + intros k; specialize (H11 k).
            simpl_Forall.
            eapply sem_block_refines; try eapply H; eauto.
            now setoid_rewrite <-Env.restrict_map.
        - (* switch *)
          econstructor; eauto.
          + eapply sem_exp_restrict...
          + simpl_Forall. do 2 esplit.
            2:{ simpl_Forall. destruct s. eapply sem_scope_restrict in H9; eauto.
                - eapply Forall_forall. intros (?&?) Hin. simpl_In. edestruct H6 as (?&Heq); eauto with senv; subst.
                  rewrite Heq. constructor.
                - intros; simpl in *. simpl_Forall; eauto. }
            destruct H2 as (Href1&Href2). split; auto.
            intros ?? Hfind. apply Env.restrict_find_inv in Hfind as (Hin&Hfind).
            eapply Href1 in Hfind as (?&Hfilter&Hfind').
            do 2 esplit; eauto. apply Env.restrict_find; auto.
            simpl_In. edestruct H6 as (?&?); eauto with senv. inv H2. solve_In.
        - (* automaton *)
          econstructor; eauto.
          + eapply sem_clock_restrict; eauto with lclocking.
          + eapply sem_transitions_restrict; eauto. simpl_Forall.
            eapply wx_exp_incl with (Γ:=Γ'); eauto with lclocking.
            intros * Hv. inv Hv. apply fst_InMembers in H7; simpl_In.
            edestruct H6 as (?&?); eauto with senv.
          + simpl_Forall. specialize (H17 k); destruct_conjs.
            esplit; split.
            2:{ destruct s. eapply sem_scope_restrict in H10; eauto.
                - eapply Forall_forall. intros (?&?) Hin. simpl_In. edestruct H6 as (?&Heq); eauto with senv; subst.
                  rewrite Heq. constructor.
                - intros; simpl in *; destruct_conjs.
                  split; simpl_Forall; eauto.
                  eapply sem_transitions_restrict; eauto. simpl_Forall; eauto with lclocking. }
            destruct H2 as (Href1&Href2). split; auto.
            intros ?? Hfind. apply Env.restrict_find_inv in Hfind as (Hin&Hfind).
            eapply Href1 in Hfind as (?&Hfilter&Hfind').
            do 2 esplit; eauto. apply Env.restrict_find; auto.
            simpl_In. edestruct H6 as (?&?); eauto with senv. inv H2. solve_In.
        - (* locals *)
          constructor. eapply sem_scope_restrict; eauto.
          intros; simpl_Forall; eauto.
      Qed.

      Corollary sem_scope_restrict1 : forall locs blk Γ H Hl bs,
          wc_env (idck Γ) ->
          wc_scope (fun Γ => Forall (wc_block G Γ)) G Γ (Scope locs blk) ->
          sem_scope_ck (fun Hi => sem_exp_ck Hi bs)
                       (fun Hi => Forall (sem_block_ck Hi bs)) (H, Hl) bs (Scope locs blk) ->
          sem_scope_ck (fun Hi => sem_exp_ck Hi bs)
                       (fun Hi => Forall (sem_block_ck Hi bs)) (Env.restrict H (map fst Γ), Hl) bs (Scope locs blk).
      Proof.
        intros.
        eapply sem_scope_restrict; eauto.
        intros; simpl_Forall; eauto using sem_block_restrict.
      Qed.

      Corollary sem_scope_restrict2 : forall locs blk def stres Γ H Hl bs,
          wc_env (idck Γ) ->
          wc_scope (fun Γ blks => Forall (wc_block G Γ) (fst blks)
                               /\ Forall (fun '(e, (_, _)) => wc_exp G Γ e /\ clockof e = [Cbase]) (snd blks))
                   G Γ (Scope locs blk) ->
          sem_scope_ck (fun Hi => sem_exp_ck Hi bs)
                       (fun Hi blks => Forall (sem_block_ck Hi bs) (fst blks)
                                    /\ sem_transitions_ck Hi bs (snd blks) def stres) (H, Hl) bs (Scope locs blk) ->
          sem_scope_ck (fun Hi => sem_exp_ck Hi bs)
                       (fun Hi blks => Forall (sem_block_ck Hi bs) (fst blks)
                                    /\ sem_transitions_ck Hi bs (snd blks) def stres)
                       (Env.restrict H (map fst Γ), Hl) bs (Scope locs blk).
      Proof.
        intros.
        eapply sem_scope_restrict; eauto.
        intros; destruct_conjs.
        split; simpl_Forall; eauto using sem_block_restrict.
        eapply sem_transitions_restrict; eauto. simpl_Forall; eauto with lclocking.
      Qed.

    End sem_restrict.

    Section sem_change_lasts.

      Fact sem_exp_change_lasts : forall Γ H Hl Hl' b e vs,
          (forall x, ~IsLast Γ x) ->
          wx_exp Γ e ->
          sem_exp_ck (H, Hl) b e vs ->
          sem_exp_ck (H, Hl') b e vs.
      Proof with eauto with datatypes.
        induction e using exp_ind2; intros * Nisl Hwt Hsem; inv Hwt; inv Hsem;
          econstructor; eauto; simpl_Forall; eauto.
        eapply Nisl in H1 as [].
        1-3:(eapply Forall2Brs_impl_In; [|eauto]; intros;
             simpl_Exists; simpl_Forall; eauto).
        specialize (H8 _ eq_refl); simpl_Forall; eauto.
      Qed.

      Lemma sem_equation_change_lasts : forall Γ H Hl Hl' b eq,
          (forall x, ~IsLast Γ x) ->
          wx_equation Γ eq ->
          sem_equation_ck (H, Hl) b eq ->
          sem_equation_ck (H, Hl') b eq.
      Proof with eauto with datatypes.
        intros ????? [xs es] Nil Hwc Hsem.
        destruct Hwc as (?&?). inv Hsem.
        econstructor. instantiate (1:=ss).
        + simpl_Forall; eauto using sem_exp_change_lasts.
        + simpl_Forall; eauto.
      Qed.

      Lemma sc_vars_change_lasts : forall Γ H Hl Hl' b,
          (forall x, ~IsLast Γ x) ->
          sc_vars Γ (H, Hl) b ->
          sc_vars Γ (H, Hl') b.
      Proof.
        intros * Hnl (Hsc1&Hsc2).
        split; eauto.
        intros * _ Hla. apply Hnl in Hla as [].
      Qed.

      Lemma sem_transitions_change_lasts : forall Γ H Hl Hl' b trans def stres,
          (forall x, ~IsLast Γ x) ->
          Forall (fun '(e, _) => wx_exp Γ e) trans ->
          sem_transitions_ck (H, Hl) b trans def stres ->
          sem_transitions_ck (H, Hl') b trans def stres.
      Proof with eauto with datatypes.
        induction trans; intros * Hnl Hwx Hsem; inv Hwx; inv Hsem;
          econstructor; eauto using sem_exp_change_lasts.
      Qed.

      Lemma sem_scope_change_lasts {A} P_nolast P_wx P_sem : forall Γ H Hl Hl' bs locs (blks: A),
          nolast_scope P_nolast (Scope locs blks) ->
          (forall x, ~IsLast Γ x) ->
          wx_scope P_wx Γ (Scope locs blks) ->
          sem_scope_ck (fun Hi => sem_exp_ck Hi bs) P_sem (H, Hl) bs (Scope locs blks) ->
          (forall Γ H Hl Hl', P_nolast blks -> (forall x, ~IsLast Γ x) -> P_wx Γ blks -> P_sem (H, Hl) blks -> P_sem (H, Hl') blks) ->
          sem_scope_ck (fun Hi => sem_exp_ck Hi bs) P_sem (H, Hl') bs (Scope locs blks).
      Proof.
        intros * Hnl Nil Hwx Hsem Hind; inv Hnl; inv Hwx; inv Hsem.
        econstructor. 3:reflexivity. all:eauto.
        - intros. simpl_Forall. congruence.
        - eapply sc_vars_change_lasts; [|eauto].
          intros * Hca. inv Hca. simpl_In. simpl_Forall. subst; simpl in *; congruence.
        - eapply Hind with (Γ:=_ ++ _); eauto.
          apply NoLast_app; split; auto.
          intros * Hca. inv Hca. simpl_In. simpl_Forall. subst; simpl in *; congruence.
      Qed.

      Lemma sem_block_change_lasts : forall blk Γ H Hl Hl' b,
          nolast_block blk ->
          (forall x, ~IsLast Γ x) ->
          wx_block Γ blk ->
          sem_block_ck (H, Hl) b blk ->
          sem_block_ck (H, Hl') b blk.
      Proof with eauto with lclocking.
        induction blk using block_ind2; intros * Hnl Nil Hwc Hsem; inv Hnl; inv Hwc; inv Hsem.
        - (* equation *)
          econstructor.
          eapply sem_equation_change_lasts...
        - (* reset *)
          econstructor; eauto.
          + eapply sem_exp_change_lasts...
          + intros k; specialize (H11 k).
            simpl_Forall. eapply H; eauto.
        - (* switch *)
          econstructor; eauto.
          + eapply sem_exp_change_lasts...
          + simpl_Forall. do 2 esplit.
            * instantiate (1:=(_,_)). destruct H3; split; simpl; eauto.
              apply Env.Equiv_Reflexive; auto using EqSt_reflex.
            * destruct s. simpl. eapply sem_scope_change_lasts; eauto.
              intros; simpl_Forall; eauto.
        - (* automaton *)
          econstructor; eauto.
          + eapply sem_transitions_change_lasts... simpl_Forall; auto.
          + simpl_Forall. specialize (H16 k); destruct_conjs.
            exists (t, (fselect_hist e k stres Hl')); split.
            * destruct H3; split; auto. reflexivity.
            * destruct s. eapply sem_scope_change_lasts; eauto.
              intros; split; destruct_conjs; simpl_Forall; eauto using sem_transitions_change_lasts.
        - (* locals *)
          constructor. eapply sem_scope_change_lasts; eauto.
          intros; simpl_Forall; eauto.
      Qed.

    End sem_change_lasts.

    Local Hint Constructors Sem.sem_exp Sem.sem_equation Sem.sem_block : lcsem.

    (** Helper lemmas for induction in the Slocal case *)
    Lemma local_hist_dom : forall xs ys (H H' : Env.t (Stream svalue)),
        Env.dom H xs ->
        Env.dom H' (map fst (Env.elements H) ++ ys) <->
        Env.dom H' (xs ++ ys).
    Proof.
      intros * Hdom1; split; intros Hdom2.
      - eapply Env.dom_intro; intros.
        eapply Env.dom_use in Hdom2. rewrite Hdom2, 2 in_app_iff.
        apply or_iff_compat_r.
        eapply Env.dom_use in Hdom1. now rewrite <-Hdom1, <-fst_InMembers, <-Env.In_Members.
      - eapply Env.dom_intro; intros.
        eapply Env.dom_use in Hdom2. rewrite Hdom2, 2 in_app_iff.
        apply or_iff_compat_r.
        eapply Env.dom_use in Hdom1. now rewrite <-Hdom1, <-fst_InMembers, <-Env.In_Members.
    Qed.

    Corollary local_hist_dom_refines {B} : forall xs (ys : list (ident * B)) H H',
        (forall x, InMembers x ys -> ~In x xs) ->
        (forall x vs, sem_var H' x vs -> ~InMembers x ys -> sem_var H x vs) ->
        Env.dom H xs ->
        Env.dom H' (map fst (Env.elements H) ++ map fst ys) ->
        Env.refines (@EqSt _) H H'.
    Proof.
      intros * Hnd Hinv Hdom1 Hdom2 ?? Hfind.
      erewrite local_hist_dom in Hdom2; eauto.
      assert (Env.In x H) as Hin by (econstructor; eauto).
      eapply Env.dom_use in Hin; eauto.
      assert (In x (xs ++ map fst ys)) as Hin' by (apply in_or_app; auto).
      eapply Env.dom_use in Hin'; eauto. destruct Hin' as (v'&Hfind2).
      assert (sem_var H' x v') as Hvar' by (econstructor; eauto; reflexivity).
      eapply Hinv in Hvar'. inv Hvar'. 2:(intro contra; eapply Hnd; eauto).
      rewrite H1 in Hfind; inv Hfind.
      do 2 eexists; eauto. now symmetry.
    Qed.

    Lemma local_hist_dom_ub : forall xs ys (H H' : Env.t (Stream svalue)),
        Env.dom_ub H xs ->
        Env.dom H' (map fst (Env.elements H) ++ ys) ->
        Env.dom_ub H' (xs ++ ys).
    Proof.
      intros * Hdom1 Hdom2.
      eapply Env.dom_ub_intro; intros. rewrite in_app_iff.
      eapply Env.dom_use in Hdom2. rewrite Hdom2, in_app_iff in H0. destruct H0 as [Hin|]; auto.
      left. eapply Env.dom_ub_use in Hdom1; eauto.
      eapply Env.dom_use; eauto using Env.dom_elements.
    Qed.

    Lemma local_hist_dom_ub_refines {B} : forall xs (ys : list (ident * B)) H H',
        (forall x, InMembers x ys -> ~In x xs) ->
        (forall x vs, sem_var H' x vs -> ~InMembers x ys -> sem_var H x vs) ->
        Env.dom_ub H xs ->
        Env.dom H' (map fst (Env.elements H) ++ map fst ys) ->
        Env.refines (@EqSt _) H H'.
    Proof.
      intros * Hnd Hinv Hdom1 Hdom2 ?? Hfind.
      assert (Env.In x H) as Hin by (econstructor; eauto).
      assert (Env.In x H') as (?&Hfind').
      { eapply Env.dom_use in Hdom2. rewrite Hdom2, in_app_iff. left.
        eapply Env.dom_use; eauto using Env.dom_elements. }
      do 2 esplit; eauto.
      eapply Env.dom_ub_use in Hin; eauto.
      assert (sem_var H' x x0) as Hvar' by (econstructor; eauto; reflexivity).
      eapply Hinv in Hvar'. inv Hvar'. 2:(intro contra; eapply Hnd; eauto).
      rewrite H1 in Hfind; inv Hfind.
      now symmetry.
    Qed.

  End ClockedSemantics.

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

  (** Morphism properties *)

  Local Hint Constructors sem_exp : lcsem.

  Add Parametric Morphism env : (sc_vars env)
      with signature history_equiv ==> @EqSt bool ==> Basics.impl
        as sc_vars_morph.
  Proof.
    intros ?? (EH1&EH2) ?? Heq2 (?&?).
    split; intros.
    - edestruct H as (?&?&?); eauto.
      esplit. split. 1,2:rewrite <-EH1; eauto.
      rewrite <-Heq2; auto.
    - edestruct H0 as (?&?&?); eauto.
      esplit. split. rewrite <-EH2; eauto.
      rewrite <-EH1, <-Heq2; auto.
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
    intros H H' EH b b' Eb e xs xs' Exs Hsem. revert H' b' xs' EH Eb Exs.
    eapply sem_exp_ck_ind2 with
        (P_exp := fun H b e xs => forall H' b' xs', history_equiv H H' -> b ≡ b' -> EqSts xs xs' -> sem_exp_ck G H' b' e xs')
        (P_equation := fun H b e => True)
        (P_transitions := fun _ _ _ _ _ => True)
        (P_block := fun H b d => True)
        (P_node := fun f xs ys => forall ys', EqSts ys ys' -> sem_node_ck G f xs ys');
      intros; eauto; unfold EqSts in *; simpl_Forall.
    - econstructor. rewrite <-H3; etransitivity; eauto; now symmetry.
    - econstructor. rewrite <-H3; etransitivity; eauto; now symmetry.
    - constructor. destruct H2 as (EH&_). now rewrite <-EH, <-H7.
    - constructor. destruct H2 as (_&EH). now rewrite <-EH, <-H7.
    - econstructor; eauto.
      + apply H2; eauto; reflexivity.
      + now rewrite <-H10.
    - econstructor; eauto.
      + apply H2; eauto; reflexivity.
      + apply H4; eauto; reflexivity.
      + now rewrite <-H13.
    - econstructor.
      + eapply Forall2_impl_In; [|apply H2].
        intros * ?? Hs; apply Hs; auto; reflexivity.
      + eapply Forall2_impl_In; [|apply H4].
        intros * ?? Hs; apply Hs; auto; reflexivity.
      + eapply Forall3_EqSt; eauto. solve_proper.
    - econstructor.
      + eapply Forall2_impl_In; [|apply H2].
        intros * ?? Hs; apply Hs; auto; reflexivity.
      + eapply Forall2_impl_In; [|apply H4].
        intros * ?? Hs; apply Hs; auto; reflexivity.
      + eapply Forall3_EqSt; eauto. solve_proper.
    - econstructor; eauto.
      + eapply Forall2_impl_In; [|apply H2].
        intros * ?? Hs; apply Hs; auto; reflexivity.
      + destruct H5 as (EH&_). rewrite <-EH; eauto.
      + eapply Forall2_EqSt; eauto. solve_proper.
    - econstructor; eauto.
      + destruct H5 as (EH&_). rewrite <-EH; eauto.
      + instantiate (1:=vs).
        eapply Forall2Brs_impl_In; [|eauto]; intros ?? Hin Hse. eapply Hse; eauto. reflexivity.
      + rewrite <-H7; auto.
    - econstructor; eauto.
      + eapply H2; eauto. reflexivity.
      + instantiate (1:=vs).
        eapply Forall2Brs_impl_In; [|eapply H4]; intros ?? _ Hs.
        eapply Hs; eauto. reflexivity.
      + eapply Forall3_EqSt_Proper; eauto. solve_proper.
    - econstructor; eauto.
      + eapply H2; eauto. reflexivity.
      + instantiate (1:=vs).
        eapply Forall2Brs_impl_In; [|eapply H5]; intros ?? _ Hs.
        eapply Hs; eauto. reflexivity.
      + instantiate (1:=vd).
        eapply Forall2_impl_In; [|apply H7]; intros ?? _ _ Hs.
        eapply Hs; eauto. reflexivity.
      + eapply Forall3_EqSt_Proper; eauto. solve_proper.
    - econstructor; eauto.
      + eapply Forall2_impl_In; [|apply H2].
        intros * ?? Hs; apply Hs; auto; reflexivity.
      + eapply Forall2_impl_In; [|apply H4].
        intros * ?? Hs; apply Hs; auto; reflexivity.
      + intro k; specialize (H6 k); destruct H6 as (?&Hr).
        apply Hr.
        apply map_st_EqSt_Proper; auto.
        intros ?? ->; reflexivity.
    - econstructor; eauto.
      eapply Forall2_EqSt; eauto. solve_proper.
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
      destruct EH as (EH&_). now rewrite <-EH.
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
      sem_scope_ck (fun Hi => sem_exp_ck G Hi bs1) P_blk1 Hi1 bs1 (Scope locs blks) ->
      history_equiv Hi1 Hi2 ->
      bs1 ≡ bs2 ->
      (forall Hi, P_blk1 Hi blks -> P_blk2 Hi blks) ->
      sem_scope_ck (fun Hi => sem_exp_ck G Hi bs2) P_blk2 Hi2 bs2 (Scope locs blks).
  Proof.
    intros * Hsem EH Eb Hind; inv Hsem.
    destruct Hi2. econstructor.
    5:rewrite <-Eb; eauto.
    - intros. destruct EH as (EH1&?). rewrite <-EH1; eauto.
    - eapply Env.dom_intro; intros. eapply Env.dom_use in H2.
      rewrite H2. rewrite 2 in_app_iff. apply or_iff_compat_r.
      destruct EH as (EH&_).
      now rewrite <-2 fst_InMembers, <-2 Env.In_Members, EH.
    - destruct EH as (?&EH2). now rewrite <-EH2.
    - intros. edestruct H4; eauto. destruct_conjs.
      do 3 esplit; eauto. repeat split; eauto.
      now rewrite <-Eb.
    - simpl_Forall.
      eapply Hind; eauto.
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
      + eapply sem_exp_ck_morph; eauto. reflexivity.
      + intros k. specialize (H4 k) as (Hsem1&Hsem1').
        eapply Forall_Forall in Hsem1; eauto. clear Hsem1'.
        eapply Forall_impl; [|eauto].
        intros ? (?&?). eapply H4; eauto.
        * destruct EH as (EH1&EH2); split; unfold Sem.mask_hist. now rewrite <-EH1. now rewrite <-EH2.
        * now rewrite <-Eb.
    - econstructor; eauto.
      + now rewrite <-EH, <-Eb.
      + simpl_Forall. inv H5.
        do 2 esplit. 2:econstructor; eauto.
        * destruct EH as (EH1&EH2); unfold filter_hist in *.
          destruct H3. split. rewrite <-EH1 at 1. eauto. rewrite <-EH2 at 1. eauto.
        * intros * Hin. edestruct H11 as (?&?&?&(?&_)&?&?&?); eauto.
          do 3 esplit. repeat (split; eauto).
          now rewrite <-Eb.
        * now rewrite <-Eb.
        * simpl_Forall. eapply H7; eauto. reflexivity. now rewrite <-Eb.
    - econstructor; eauto.
      + destruct EH as (EH1&EH2). rewrite <-EH1, <-Eb; eauto.
      + now rewrite <-EH.
      + simpl_Forall. specialize (H4 k) as ((Hik&Hikl)&?). destruct_conjs.
        inv H6; destruct_conjs.
        exists (Hik, Hikl). split; [|econstructor]; eauto.
        * destruct EH as (EH1&EH2). destruct H4 as (Hsel1&Hsel2).
          split. rewrite <-EH1; auto. rewrite <-EH2; auto.
        * intros * Hin. edestruct H12 as (?&?&?&(?&_)&?&?&?); eauto.
          do 3 esplit. repeat (split; eauto).
          now rewrite <-Eb.
        * now rewrite <-Eb.
        * split; simpl_Forall. eapply H7; eauto. reflexivity. 1,2:now rewrite <-Eb.
    - constructor. destruct Hi, H'.
      inv H0; econstructor. 5:rewrite <-Eb; eauto.
      + intros. destruct EH as (EH1&?). rewrite <-EH1; eauto.
      + eapply Env.dom_intro; intros. eapply Env.dom_use in H4.
        rewrite H4. rewrite 2 in_app_iff. apply or_iff_compat_r.
        destruct EH as (EH&_).
        now rewrite <-2 fst_InMembers, <-2 Env.In_Members, EH.
      + destruct EH as (?&EH2). now rewrite <-EH2.
      + intros. edestruct H6; eauto. destruct_conjs.
        do 3 esplit; eauto. repeat split; eauto.
        now rewrite <-Eb.
      + simpl_Forall.
        eapply H2; eauto. reflexivity.
  Qed.

  Add Parametric Morphism {PSyn prefs} (G: @global PSyn prefs) : (sem_node_ck G)
      with signature eq ==> @EqSts svalue ==> @EqSts svalue ==> Basics.impl
        as sem_node_ck_morph.
  Proof.
    unfold Basics.impl; intros f xss xss' Exss yss yss' Eyss Sem.
    induction Sem.
    subst.
    econstructor; try reflexivity; eauto.
    + instantiate (1 := H). now rewrite <-Exss.
    + now rewrite <-Eyss.
    + eapply sem_block_ck_morph; eauto. reflexivity.
      now rewrite <-Exss.
    + eapply clocked_node_morph; eauto.
      now rewrite <-Exss.
  Qed.

  (** ** Properties of the [global] environment *)

  Ltac sem_block_cons :=
    match goal with
    | H:sem_scope_ck _ _ _ _ _ |- sem_scope_ck _ _ _ _ _ =>
        inv H; destruct_conjs; econstructor; eauto
    | _ => Sem.sem_block_cons
    end.

  Lemma sem_block_ck_cons {PSyn prefs} :
    forall (nd : @node PSyn prefs) nds enums bck Hi bk,
      Ordered_nodes (Global enums (nd::nds))
      -> sem_block_ck (Global enums (nd::nds)) Hi bk bck
      -> ~Is_node_in_block nd.(n_name) bck
      -> sem_block_ck (Global enums nds) Hi bk bck.
  Proof.
    intros * Hord Hsem Hnf.
    revert Hnf.
    eapply sem_block_ck_ind2
      with
        (P_exp := fun H bk e ss => ~ Is_node_in_exp nd.(n_name) e
                                -> sem_exp_ck (Global enums0 nds) H bk e ss)
        (P_equation := fun H bk eq => ~Is_node_in_eq nd.(n_name) eq
                                   -> sem_equation_ck (Global enums0 nds) H bk eq)
        (P_transitions := fun bk H trans default stres => ~List.Exists (fun '(e, _) => Is_node_in_exp nd.(n_name) e) trans
                                                       -> sem_transitions_ck (Global enums0 nds) bk H trans default stres)
        (P_block := fun H bk d => ~Is_node_in_block nd.(n_name) d
                               -> sem_block_ck (Global enums0 nds) H bk d)
        (P_node := fun f ins outs => nd.(n_name) <> f
                                  -> sem_node_ck (Global enums0 nds) f ins outs). 23:eauto.
    all:econstructor; eauto; repeat sem_block_cons.
    - eapply find_node_later_not_Is_node_in; eauto.
  Qed.

  Corollary sem_node_ck_cons {PSyn prefs} :
    forall (nd : @node PSyn prefs) nds enums f xs ys,
      Ordered_nodes (Global enums (nd::nds))
      -> sem_node_ck (Global enums (nd::nds)) f xs ys
      -> nd.(n_name) <> f
      -> sem_node_ck (Global enums nds) f xs ys.
  Proof.
    intros * Hord Hsem Hnf. inv Hsem.
    rewrite find_node_other with (1:=Hnf) in H0.
    econstructor; eauto.
    eapply sem_block_ck_cons; eauto.
    apply find_node_later_not_Is_node_in with (1:=Hord) in H0; eauto.
  Qed.

  Lemma sem_block_ck_cons' {PSyn prefs} :
    forall (nd : @node PSyn prefs) nds enums bck Hi bk,
      Ordered_nodes (Global enums (nd::nds))
      -> sem_block_ck (Global enums nds) Hi bk bck
      -> ~Is_node_in_block nd.(n_name) bck
      -> sem_block_ck (Global enums (nd::nds)) Hi bk bck.
  Proof.
    intros * Hord Hsem Hnf.
    revert Hnf.
    eapply sem_block_ck_ind2
      with
        (P_exp := fun H bk e ss => ~ Is_node_in_exp nd.(n_name) e
                                -> sem_exp_ck (Global enums0 (nd::nds)) H bk e ss)
        (P_equation := fun H bk eq => ~Is_node_in_eq nd.(n_name) eq
                                   -> sem_equation_ck (Global enums0 (nd::nds)) H bk eq)
        (P_transitions := fun bk H trans default stres => ~List.Exists (fun '(e, _) => Is_node_in_exp nd.(n_name) e) trans
                                                       -> sem_transitions_ck (Global enums0 (nd::nds)) bk H trans default stres)
        (P_block := fun H bk d => ~Is_node_in_block nd.(n_name) d
                               -> sem_block_ck (Global enums0 (nd::nds)) H bk d)
        (P_node := fun f ins outs => nd.(n_name) <> f
                                  -> sem_node_ck (Global enums0 (nd::nds)) f ins outs). 23:eauto.
    all:econstructor; eauto; repeat sem_block_cons.
    - eapply find_node_later_not_Is_node_in; eauto.
  Qed.

  Corollary sem_node_ck_cons' {PSyn prefs} :
    forall (nd : @node PSyn prefs) nds enums f xs ys,
      Ordered_nodes (Global enums (nd::nds))
      -> sem_node_ck (Global enums nds) f xs ys
      -> nd.(n_name) <> f
      -> sem_node_ck (Global enums (nd::nds)) f xs ys.
  Proof.
    intros * Hord Hsem Hnf. inv Hsem.
    econstructor; eauto.
    - erewrite find_node_other; eauto.
    - eapply sem_block_ck_cons'; eauto.
    apply find_node_later_not_Is_node_in with (1:=Hord) in H0; auto.
  Qed.

  Lemma sem_node_ck_cons_iff {PSyn prefs} :
    forall (n : @node PSyn prefs) nds enums f xs ys,
      Ordered_nodes (Global enums (n::nds)) ->
      n_name n <> f ->
      sem_node_ck (Global enums nds) f xs ys <->
      sem_node_ck (Global enums (n::nds)) f xs ys.
  Proof.
    intros * Hord Hname.
    split; intros Hsem.
    - eapply sem_node_ck_cons'; eauto.
    - eapply sem_node_ck_cons; eauto.
  Qed.

  (* Go back from clocked semantics to semantics *)
  Section sem_ck_sem.
    Context {PSyn : block -> Prop}.
    Context {prefs: PS.t}.
    Variable G : @global PSyn prefs.

    Lemma sem_exp_ck_sem_exp : forall H b e vs,
        sem_exp_ck G H b e vs ->
        sem_exp G H b e vs.
    Proof.
      intros * Hsem.
      eapply sem_exp_ck_ind2 with
          (P_equation := fun H b eq => sem_equation G H b eq)
          (P_transitions := fun H b trans default stres => sem_transitions G H b trans default stres)
          (P_block := fun H b blk => sem_block G H b blk)
          (P_node := fun f xs ys => sem_node G f xs ys). 23:eauto.
      all:intros; econstructor; eauto.
      1,2:intros k.
      - specialize (H6 k) as (?&?); auto.
      - specialize (H4 k) as (?&?); auto.
      - simpl_Forall; eauto.
        do 2 esplit; eauto. inv H5; econstructor; eauto.
        + intros. edestruct H11; eauto; destruct_conjs.
          do 3 esplit. repeat split; eauto.
        + simpl_Forall; eauto.
      - simpl_Forall. specialize (H4 k); destruct_conjs.
        do 2 esplit; eauto. inv H6; econstructor; eauto.
        + intros. edestruct H12; eauto; destruct_conjs.
          do 3 esplit. repeat split; eauto.
        + destruct_conjs; split; simpl_Forall; eauto.
      - inv H0; econstructor; eauto.
        + intros. edestruct H4; eauto; destruct_conjs.
          do 3 esplit. repeat split; eauto.
        + simpl_Forall; eauto.
    Qed.

    Corollary sem_exps_ck_sem_exps : forall H b es vs,
        Forall2 (sem_exp_ck G H b) es vs ->
        Forall2 (sem_exp G H b) es vs.
    Proof.
      intros.
      eapply Forall2_impl_In; [|eauto]; intros.
      eapply sem_exp_ck_sem_exp; eauto.
    Qed.

    Corollary sem_transitions_ck_sem_transitions : forall Hi bs trans def stres,
        sem_transitions_ck G Hi bs trans def stres ->
        sem_transitions G Hi bs trans def stres.
    Proof.
      induction trans; intros * Htr; inv Htr;
        econstructor; eauto using sem_exp_ck_sem_exp.
    Qed.

  End sem_ck_sem.

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

  Local Hint Resolve Env.find_1 Env.find_2 : lcsem.

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
                     orel (fun v1 v2 => EqSt v1 (maskv k rs v2)) (Env.find x H) (Env.find x' H'))) ->
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
    assert (forall x x', Is_free_in_clock x ck -> sub x = Some x' -> orel (@eq svalue) (Env.find x (CIStr.tr_history H n)) (Env.find x' (CIStr.tr_history H' n))) as Henv'.
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
          orel (fun v1 v2 => EqSt v1 (maskv k rs v2)) (Env.find x H) (Env.find x' H')) ->
      sem_clock H (maskb k rs b) ck (maskb k rs cks).
  Proof with eauto with lcsem.
    intros * Hinst Hck Hbck Henv.
    rewrite sem_clock_equiv in *.
    intros n. specialize (Hck n). specialize (Hbck n).
    assert (forall x x' n, Is_free_in_clock x ck -> sub x = Some x' -> orel (fun v1 v2 => v1 = (if (CStr.count rs) # n =? k then v2 else absent)) (Env.find x (CIStr.tr_history H n)) (Env.find x' (CIStr.tr_history H' n))) as Henv'.
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
        orel (fun v1 v2 => v1 ≡ maskv k rs v2) (Env.find i Hi) (Env.find i' H).
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
    simpl in H2; inv H2. apply Env.find_1 in H5; rewrite H5.
    inv Hinst; simpl in *. rewrite Sub in H2; inv H2.
    simpl in H3; inv H3. apply Env.find_2 in H7; rewrite H7.
    constructor. symmetry. rewrite <- H8; eauto.
  Qed.

  (* When function call parameters are well instantiated and have
     the [sem_clock] property, we obtain the same property inside
     the node (Hi = "H inside").
   *)
  Corollary sc_inside_mask {PSyn prefs} :
    forall H Hi b es ss0 bck sub (n : @node PSyn prefs) k rs,
      Forall2 (fun '(_, o) (s : Stream svalue) => LiftO True (fun x1 : ident => sem_var H x1 s) o) (nclocksof es) (concat ss0) ->
      wc_env (map (fun '(x, (_, ck, _)) => (x, ck)) (n_in n)) ->
      Forall2 (sem_clock H b) (clocksof es) (map abstract_clock (concat ss0)) ->
      Forall2 (WellInstantiated bck sub) (map (fun '(x, (_, ck, _)) => (x, ck)) (n_in n)) (nclocksof es) ->
      Forall2 (sem_var Hi) (idents (n_in n)) (map (maskv k rs) (concat ss0)) ->
      Forall2 (fun xc => sem_clock Hi (clocks_of (map (maskv k rs) (concat ss0))) (snd xc))
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
      unfold idents in Hsv. simpl_Forall. auto.
  Qed.

  Definition def_stream b := enum b 0.

  Lemma sc_outside_mask {PSyn1 PSyn2 prefs1 prefs2} :
    forall (G : @global PSyn1 prefs1) H es b Γ ncks ss0 ss bck sub (n : @node PSyn2 prefs2) rs,
      Forall (wc_exp G Γ) es ->
      Forall2 (fun '(_, o1) s => LiftO True (fun x0 : ident => sem_var H x0 s) o1) (nclocksof es) (concat ss0) ->
      Forall2 (fun '(_, o) s => LiftO True (fun x0 => sem_var H x0 s) o) ncks ss ->
      wc_env (map (fun '(x, (_, ck, _)) => (x, ck)) (n_in n)) ->
      wc_env (map (fun '(x, (_, ck, _)) => (x, ck)) (n_in n ++ n_out n)) ->
      Forall2 (sem_clock H b) (clocksof es) (map abstract_clock (concat ss0)) ->
      Forall2 (WellInstantiated bck sub) (map (fun '(x, (_, ck, _)) => (x, ck)) (n_in n)) (nclocksof es) ->
      Forall2 (WellInstantiated bck sub) (map (fun '(x, (_, ck, _)) => (x, ck)) (n_out n)) ncks ->
      (forall k, exists Hi,
            Forall2 (fun xc => sem_clock Hi (clocks_of (map (maskv k rs) (concat ss0))) (snd xc))
                    (map (fun '(x, (_, ck, _)) => (x, ck)) (n_out n)) (map abstract_clock (map (maskv k rs) ss)) /\
            Forall2 (sem_var Hi) (idents (n_in n)) (map (maskv k rs) (concat ss0)) /\
            Forall2 (sem_var Hi) (idents (n_out n)) (map (maskv k rs) ss)) ->
      Forall2 (sem_clock H b) (map fst ncks) (map abstract_clock ss).
  Proof.
    intros * Hwc Hsvar Hse2 WCin WCinout Hscin WIi WIo Hk.

    rewrite clocksof_nclocksof, Forall2_map_1, Forall2_map_2 in Hscin.
    rewrite Forall2_map_1, Forall2_map_2.
    assert (length ncks = length (n_out n)) as Hlen1.
    { apply Forall2_length in WIo. now rewrite map_length in WIo. }
    assert (length ncks = length ss) as Hlen2.
    { specialize (Hk 0) as (?&_&_&Hf).
      unfold idents in Hf. simpl_Forall. apply Forall2_length in Hf.
      congruence. }
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
      exists Hi. split.
      + eapply Forall2_forall2 in H0 as [? Hck].
        rewrite Hlen1 in Hlen. setoid_rewrite map_length in Hck.
        specialize (Hck (xH, Cbase) (abstract_clock (def_stream b)) _ _ _ Hlen eq_refl eq_refl).
        erewrite clocks_of_mask in Hck.
        setoid_rewrite map_nth' with (l:=map _ _) (d':=Streams.const absent) in Hck. erewrite map_nth' with (l:=ss), ac_mask in Hck; eauto.
        2:rewrite map_length. 1,2:congruence.
      + intros i i' Free Sub.
        destruct (nth n0 (map (fun '(x, (_, ck, _)) => (x, ck)) (n_out n)) (1%positive, Cbase)) as (yck, ny) eqn:Hy.
        assert (In (yck, ny) (map (fun '(x, (_, ck, _)) => (x, ck)) (n_in n ++ n_out n))) as Hyin2.
        { rewrite map_app. apply in_or_app. right.
          rewrite <- Hy. apply nth_In. rewrite map_length. congruence. }
        pose proof (wc_env_free_in_clock _ _ _ _ WCinout Hyin2 Free) as [].
        eapply inst_in_eqst_mask with (vs:=(concat ss0++ss)). 1,5:eauto.
        * rewrite map_app. eapply Forall2_app; eauto.
        * unfold idents in *. simpl_Forall. apply Forall2_app; simpl_Forall; eauto.
        * eapply Forall2_app; eauto.
  Qed.

  Definition sem_clock_inputs {PSyn prefs} (G : @global PSyn prefs) (f : ident) (xs : list (Stream svalue)): Prop :=
    exists H n,
      find_node f G = Some n /\
      Forall2 (sem_var H) (idents (n_in n)) xs /\
      Forall2 (fun xc => sem_clock H (clocks_of xs) (snd xc))
              (map (fun '(x, (_, ck, _)) => (x, ck)) (n_in n)) (map abstract_clock xs).

  Lemma sem_clock_inputs_cons {PSyn prefs} :
    forall enums (nodes : list (@node PSyn prefs)) f n ins,
      n_name n <> f ->
      sem_clock_inputs (Global enums nodes) f ins <-> sem_clock_inputs (Global enums (n :: nodes)) f ins.
  Proof.
    intros * Hname.
    split; intros (H & n' & Hfind &?&?);
      exists H, n'; repeat split; auto.
    - rewrite find_node_other; eauto.
    - erewrite <- find_node_other; eauto.
  Qed.

  Lemma inputs_clocked_vars {PSyn prefs} :
    forall enums (nodes : list (@node PSyn prefs)) n H f ins,
      sem_clock_inputs (Global enums (n :: nodes)) f ins ->
      n_name n = f ->
      wc_env (map (fun '(x, (_, ck, _)) => (x, ck)) (n_in n)) ->
      Forall2 (sem_var H) (idents (n_in n)) ins ->
      Forall2 (fun xc => sem_clock H (clocks_of ins) (snd xc)) (map (fun '(x, (_, ck, _)) => (x, ck)) (n_in n)) (map abstract_clock ins).
  Proof.
    intros * (H'&n'& Hfind & Hv & Hscin) Hnf Wcin Hins; subst.
    rewrite find_node_now in Hfind; auto. inv Hfind.
    pose proof (sem_var_env_eq _ _ _ _ Hins Hv) as Horel.
    eapply Forall2_impl_In; [|eauto]. intros; simpl in *.
    eapply sem_clock_same_find; eauto.
    - unfold wc_env in Wcin. simpl_In. simpl_Forall. eapply Wcin.
    - unfold idents in *. simpl_Forall. auto.
  Qed.

  Lemma sem_clocks_det : forall H H' b ins outs vins vouts ss,
      wc_env (map (fun '(x, (_, ck, _)) => (x, ck)) (ins ++ outs)) ->
      Forall2 (sem_var H) (idents ins) vins ->
      Forall2 (sem_var H) (idents outs) vouts ->
      Forall2 (sem_var H') (idents ins) vins ->
      Forall2 (sem_var H') (idents outs) vouts ->
      Forall2 (fun xc => sem_clock H b (snd xc)) (map (fun '(x, (_, ck, _)) => (x, ck)) outs) ss ->
      Forall2 (fun xs => sem_clock H' b (snd xs)) (map (fun '(x, (_, ck, _)) => (x, ck)) outs) ss.
  Proof.
    intros * Hwc Hi1 Ho1 Hi2 Ho2 Hck.
    eapply Forall2_impl_In; [|eauto]. intros [? ?] ? Hin1 Hin2 Hsc.
    rewrite map_app in Hwc. assert (Hwc':=Hwc). apply Forall_app_weaken in Hwc.
    eapply Forall_forall in Hin1; eauto; simpl in *.
    rewrite sem_clock_equiv in *. clear Hck Hwc Hwc' Hin2.
    intros n. specialize (Hsc n).
    eapply Forall2_app in Ho1; [|eapply Hi1]. eapply Forall2_app in Ho2; [|eapply Hi2]. clear Hi1 Hi2.
    unfold idents in Ho1, Ho2. rewrite <- map_app, Forall2_map_1 in Ho1, Ho2.
    assert (Forall2 (fun x => IStr.sem_var_instant (CIStr.tr_history H n) (fst x)) (ins ++ outs)
                    (map (fun x => tr_Stream x n) (vins ++ vouts))) as Ho.
    { rewrite Forall2_map_2. eapply Forall2_impl_In; [|eapply Ho1]. intros (?&?&?) ? ? ? ?.
      eapply CIStr.sem_var_impl in H2; eauto. } clear Ho1.
    assert (Forall2 (fun x => IStr.sem_var_instant (CIStr.tr_history H' n) (fst x)) (ins ++ outs)
                    (map (fun x => tr_Stream x n) (vins ++ vouts))) as Ho'.
    { rewrite Forall2_map_2. eapply Forall2_impl_In; [|eapply Ho2]. intros (?&?&?) ? ? ? ?.
      eapply CIStr.sem_var_impl in H2; eauto. } clear Ho2.
    assert (Forall (fun '(x, _) => forall v, IStr.sem_var_instant (CIStr.tr_history H n) x v -> IStr.sem_var_instant (CIStr.tr_history H' n) x v)
                   (map (fun '(x, (_, ck, _)) => (x, ck)) (ins ++ outs))) as Hvars.
    { simpl_Forall.
      eapply Forall2_ignore2 in Ho'. simpl_Forall.
      intros ? Hvar. eapply IStr.sem_var_instant_det in H2; eauto; subst. assumption.
    } clear Ho Ho'.
    rewrite <-map_app in Hin1.

    revert b b0 Hsc.
    induction Hin1; intros; inv Hsc; [eapply IStr.Sbase|eapply IStr.Son|eapply IStr.Son_abs1|eapply IStr.Son_abs2]; eauto.
    - rewrite H5. eapply IHHin1. congruence.
    - simpl_Forall; eauto.
    - rewrite H5. eapply IHHin1. congruence.
    - simpl_Forall; eauto.
    - specialize (IHHin1 b0 (Streams.const true)). rewrite tr_Stream_const in IHHin1; eauto.
    - simpl_Forall; eauto.
  Qed.

  (** First step of the proof:
      Prove that every named stream of the node is aligned with the clock
      of its variable *)
  Section sc_inv.
    Context {PSyn : block -> Prop}.
    Context {prefs : PS.t}.
    Variable (G : @global PSyn prefs).

    Hypothesis Hnode : forall f ins outs,
        sem_node G f ins outs ->
        sem_clock_inputs G f ins ->
        sem_node_ck G f ins outs.

    Lemma Hscnodes :
      forall G1 H f n xs (* vs *) os,
        wc_node G1 n ->
        Sem.sem_node G f xs os ->
        find_node f G = Some n ->
        Forall2 (sem_var H) (idents (n_in n)) xs ->
        Forall2 (sem_var H) (idents (n_out n)) os ->
        Forall2 (fun xc => sem_clock H (clocks_of xs) (snd xc))
                (map (fun '(x, (_, ck, _)) => (x, ck)) (n_in n)) (map abstract_clock xs) ->
        Forall2 (fun xc => sem_clock H (clocks_of xs) (snd xc))
                (map (fun '(x, (_, ck, _)) => (x, ck)) (n_out n)) (map abstract_clock os).
    Proof.
      intros * Hwc Hsem Hfind Hins Houts Hckins.
      eapply Hnode in Hsem. 2:(repeat esplit; eauto).
      destruct Hwc as (_&Hwc&_). inv Hsem.
      rewrite Hfind in H1. inv H1.
      eapply sem_clocks_det; eauto.
      unfold idents in *. simpl_Forall.
      destruct H6 as (_&(?&Hvar&?)&_). 1:econstructor; solve_In; eauto using in_or_app; eauto.
      simpl in *. eapply sem_var_det in H8; eauto.
      rewrite <-H8; auto.
    Qed.

    Definition sc_var_inv Γ (H : Sem.history) (b : Stream bool) : ident -> Prop :=
      fun cx =>
        (forall x ck xs,
            HasCaus Γ x cx ->
            HasClock Γ x ck ->
            sem_var (fst H) x xs ->
            sem_clock (fst H) b ck (abstract_clock xs))
        /\ (forall x ck xs,
              HasLastCaus Γ x cx ->
              HasClock Γ x ck ->
              sem_var (snd H) x xs ->
              sem_clock (fst H) b ck (abstract_clock xs)).

    Lemma sc_vars_sc_var_inv : forall Γ H b,
        sc_vars Γ H b ->
        Forall (sc_var_inv Γ H b) (map snd (idcaus_of_senv Γ)).
    Proof.
      intros * (Hinv1&Hinv2).
      simpl_Forall. split; intros * Hca Hck Hvar.
      - edestruct Hinv1 as (?&Hvar'&?); eauto.
        eapply sem_var_det in Hvar; eauto. now rewrite <-Hvar.
      - edestruct Hinv2 as (?&Hvar'&?); eauto.
        inv Hca; econstructor; eauto. congruence.
        eapply sem_var_det in Hvar; eauto.
        now rewrite <-Hvar.
    Qed.

    Lemma sc_var_inv_sc_vars : forall Γ H b,
        NoDupMembers Γ ->
        (forall x, IsVar Γ x -> exists v, sem_var (fst H) x v) ->
        (forall x, IsLast Γ x -> exists v, sem_var (snd H) x v) ->
        Forall (sc_var_inv Γ H b) (map snd (idcaus_of_senv Γ)) ->
        sc_vars Γ H b.
    Proof.
      intros * Hnd Hv1 Hv2 Hinv.
      unfold idcaus_of_senv in Hinv. rewrite map_app in Hinv.
      apply Forall_app in Hinv as (Hinv1&Hinv2).
      unfold sc_vars. split; intros * Hck; [|intros Hca].
      - inv Hck.
        edestruct Hv1 as (?&Hvar); eauto with senv.
        eapply Forall_forall in Hinv1 as (Hinv1&_). 2:solve_In. simpl in *.
        do 2 esplit; eauto.
        eapply Hinv1; eauto. 1,2:econstructor; solve_In; eauto.
      - inv Hck. inv Hca. eapply NoDupMembers_det in H0; eauto; subst.
        edestruct Hv2 as (?&Hvar).
        1:{ econstructor; eauto. }
        destruct (causl_last _) eqn:Hcaus; try congruence.
        eapply Forall_forall in Hinv2 as (_&Hinv2). 2:solve_In; rewrite Hcaus; simpl; eauto.
        do 2 esplit; eauto.
        eapply Hinv2; eauto. 1,2:econstructor; solve_In; eauto.
    Qed.

    Definition sc_exp_inv Γ Γty H b : exp -> nat -> Prop :=
      fun e k => forall ss,
          wt_exp G Γty e ->
          wc_exp G Γ e ->
          Sem.sem_exp G H b e ss ->
          sem_clock (fst H) b (nth k (clockof e) Cbase) (abstract_clock (nth k ss (def_stream b))).

    Fact P_exps_sc_exp_inv : forall Γ Γty H b es ss k,
        Forall (wt_exp G Γty) es ->
        Forall (wc_exp G Γ) es ->
        Forall2 (Sem.sem_exp G H b) es ss ->
        P_exps (sc_exp_inv Γ Γty H b) es k ->
        sem_clock (fst H) b (nth k (clocksof es) Cbase) (abstract_clock (nth k (concat ss) (def_stream b))).
    Proof.
      induction es; intros * Hwt Hwc Hsem Hp;
        inv Hwt; inv Hwc; inv Hsem; simpl. inv Hp.
      assert (length y = numstreams a) as Hlen by (eapply sem_exp_numstreams; eauto with ltyping).
      inv Hp.
      - (* now *)
        rewrite app_nth1. 2:rewrite length_clockof_numstreams; auto.
        rewrite app_nth1. 2:congruence.
        eapply H10; eauto.
      - (* later *)
        rewrite app_nth2. 1,2:rewrite length_clockof_numstreams; auto.
        rewrite app_nth2. 1,2:rewrite Hlen; auto.
    Qed.

    Fact Forall2Brs_sc_exp_inv1 : forall Γ Γty H b ck x tx es k ss,
        k < length ss ->
        Forall (fun es => Forall (wt_exp G Γty) (snd es)) es ->
        Forall (fun es => Forall (wc_exp G Γ) (snd es)) es ->
        Forall (fun '(i, es0) => Forall (eq (Con ck x (tx, i))) (clocksof es0)) es ->
        Forall (fun es0 => length ss = length (clocksof (snd es0))) es ->
        Forall2Brs (Sem.sem_exp G H b) es ss ->
        Forall (fun es => P_exps (sc_exp_inv Γ Γty H b) (snd es) k) es ->
        Forall (fun '(i, v) => sem_clock (fst H) b (Con ck x (tx, i)) (abstract_clock v)) (nth k ss []).
    Proof.
      induction es; intros * Hlen Hwt Hwc Hck1 Hck2 Hsem Hp;
        inv Hwt; inv Hwc; inv Hck1; inv Hck2; inv Hsem; inv Hp; simpl.
      1:{ eapply Forall_forall in H0; [|eapply nth_In]; eauto.
          rewrite H0; auto. }
      eapply P_exps_sc_exp_inv in H12 as Heq1. 4:eauto. 2-3:eauto.
      eapply IHes in H14 as Heq2. 7:eauto. 2-6:eauto.
      2,3:(eapply Forall3_length in H13 as (Hlen1&Hlen2); rewrite Hlen2; auto).
      clear - Hlen H6 H8 H13 Heq1 Heq2.
      eapply Forall3_forall3 in H13 as (?&?&?).
      erewrite H2 at 1; try reflexivity. 2:congruence.
      constructor; eauto; simpl in *.
      eapply Forall_forall in H6; [|eapply nth_In; setoid_rewrite <-H8; eauto].
      erewrite <-H6 in Heq1; eauto.
    Qed.

    Fact P_exps_sc_exp_inv_all : forall Γ Γty H b es ss,
        Forall (wt_exp G Γty) es ->
        Forall (wc_exp G Γ) es ->
        Forall2 (Sem.sem_exp G H b) es ss ->
        (forall k, k < length (annots es) -> P_exps (sc_exp_inv Γ Γty H b) es k) ->
        Forall2 (sem_clock (fst H) b) (clocksof es) (map abstract_clock (concat ss)).
    Proof.
      intros * Hwt Hwc Hsem Hk.
      assert (length (clocksof es) = length (concat ss)) as Hlen.
      { rewrite length_clocksof_annots. symmetry.
        eapply sem_exps_numstreams; eauto with ltyping. }
      eapply Forall2_forall2; split. rewrite map_length; auto.
      intros * Hn ? ?; subst.
      erewrite map_nth' with (d':=def_stream b). 2:congruence.
      erewrite nth_indep with (d':=Cbase); auto.
      eapply P_exps_sc_exp_inv; eauto.
      eapply Hk. rewrite <- length_clocksof_annots; auto.
    Qed.

    Lemma sc_exp_const : forall Γ Γty H b c,
        sc_exp_inv Γ Γty H b (Econst c) 0.
    Proof.
      intros * ? _ Hwc Hsem; inv Hsem.
      simpl. rewrite H4, ac_const.
      constructor. reflexivity.
    Qed.

    Lemma sc_exp_enum : forall Γ Γty H b k ty,
        sc_exp_inv Γ Γty H b (Eenum k ty) 0.
    Proof.
      intros * ? _ Hwc Hsem; inv Hsem.
      simpl. rewrite H6, ac_enum.
      constructor. reflexivity.
    Qed.

    Lemma sc_exp_var : forall Γ Γty H b x cx ann,
        HasCaus Γ x cx ->
        sc_var_inv Γ H b cx ->
        sc_exp_inv Γ Γty H b (Evar x ann) 0.
    Proof.
      intros * (* 1 Hnd2 *) Hin (Hvar&_) ss _ Hwc Hsem; inv Hsem; simpl.
      eapply Hvar; [eauto| |eauto].
      inv Hwc; auto.
    Qed.

    Lemma sc_exp_last : forall Γ Γty H b x cx ann,
        HasLastCaus Γ x cx ->
        sc_var_inv Γ H b cx ->
        sc_exp_inv Γ Γty H b (Elast x ann) 0.
    Proof.
      intros * (* 1 Hnd2 *) Hin (_&Hvar) ss _ Hwc Hsem; inv Hsem; simpl.
      eapply Hvar; [eauto| |eauto].
      inv Hwc; auto.
    Qed.

    Lemma sc_exp_unop : forall Γ Γty H b op e1 ann,
        sc_exp_inv Γ Γty H b e1 0 ->
        sc_exp_inv Γ Γty H b (Eunop op e1 ann) 0.
    Proof.
      intros * He1 ss Hwt Hwc Hsem; inv Hwt; inv Hwc; inv Hsem; simpl.
      eapply He1 in H13; eauto. rewrite H10 in H13; simpl in H13.
      rewrite <- ac_lift1; eauto.
    Qed.

    Lemma sc_exp_binop : forall Γ Γty H b op e1 e2 ann,
        sc_exp_inv Γ Γty H b e1 0 ->
        sc_exp_inv Γ Γty H b e2 0 ->
        sc_exp_inv Γ Γty H b (Ebinop op e1 e2 ann) 0.
    Proof.
      intros * He1 He2 ss Hwt Hwc Hsem; inv Hwt; inv Hwc; inv Hsem; simpl.
      eapply He1 in H16; eauto. rewrite H14 in H16; simpl in H14.
      rewrite <- ac_lift2; eauto.
    Qed.

    Lemma sc_exp_fby : forall Γ Γty H b e0s es ann k,
        k < length ann ->
        P_exps (sc_exp_inv Γ Γty H b) e0s k ->
        sc_exp_inv Γ Γty H b (Efby e0s es ann) k.
    Proof.
      intros * Hk Hexps ss Hwt Hwc Hsem; simpl.
      inv Hwt. inv Hwc. inv Hsem.
      eapply P_exps_sc_exp_inv in Hexps; eauto.
      rewrite Forall2_eq in H10. rewrite H10.
      assert (Forall2 (fun x y => abstract_clock x ≡ abstract_clock y) (concat s0ss) ss).
      { clear - H18. eapply Forall3_ignore2 in H18.
        eapply Forall2_impl_In; eauto.
        intros ? ? _ _ [? ?]. apply ac_fby1 in H; auto. }
      apply Forall2_forall2 in H0 as [_ Hac].
      erewrite <- Hac; eauto.
      erewrite sem_exps_numstreams, <- length_clocksof_annots, <- H10, map_length; eauto with ltyping.
    Qed.

    Lemma sc_exp_arrow : forall Γ Γty H b e0s es ann k,
        k < length ann ->
        P_exps (sc_exp_inv Γ Γty H b) e0s k ->
        P_exps (sc_exp_inv Γ Γty H b) es k ->
        sc_exp_inv Γ Γty H b (Earrow e0s es ann) k.
    Proof.
      intros * Hk He0s Hes ss Hwt Hwc Hsem; simpl.
      inv Hwt. inv Hwc. inv Hsem.
      eapply P_exps_sc_exp_inv in He0s; eauto.
      rewrite Forall2_eq in H10. rewrite H10.
      assert (Forall2 (fun x y => abstract_clock x ≡ abstract_clock y) (concat s0ss) ss).
      { clear - H18. eapply Forall3_ignore2 in H18.
        eapply Forall2_impl_In; eauto.
        intros ? ? _ _ [? ?]. apply ac_arrow1 in H; auto. }
      apply Forall2_forall2 in H0 as [_ Hac].
      erewrite <- Hac; eauto.
      erewrite sem_exps_numstreams, <- length_clocksof_annots, <- H10, map_length; eauto with ltyping.
    Qed.

    Lemma sc_exp_when : forall Γ Γty H b es x cx b' ann k,
        NoDupMembers Γ ->
        k < length (fst ann) ->
        P_exps (sc_exp_inv Γ Γty H b) es k ->
        HasCaus Γ x cx ->
        sc_var_inv Γ H b cx ->
        sc_exp_inv Γ Γty H b (Ewhen es x b' ann) k.
    Proof.
      intros * Hnd Hk Hes Hin Hvar ss Hwt Hwc Hsem; simpl.
      inv Hwt. inv Hwc. inv Hsem.
      eapply P_exps_sc_exp_inv in Hes; eauto.
      assert (Hv:=H18). eapply Hvar in Hv; eauto.
      erewrite map_nth' with (d':=OpAux.bool_velus_type); eauto.
      eapply Forall_forall in H12. 2:eapply nth_In; rewrite <- H13; eauto.
      eapply sc_when in Hes; eauto. erewrite H12; eauto.
      eapply Forall2_forall2 in H19 as [_ Hwhen].
      eapply Hwhen; eauto.
      replace (length (concat ss0)) with (length (annots es)). rewrite <- length_clocksof_annots, <- H13; eauto.
      symmetry. eapply sem_exps_numstreams; eauto with ltyping.
    Qed.

    Lemma sc_exp_merge : forall Γ Γty H b x cx tx es ann k,
        NoDupMembers Γ ->
        k < length (fst ann) ->
        HasCaus Γ x cx ->
        sc_var_inv Γ H b cx ->
        Forall (fun es => P_exps (sc_exp_inv Γ Γty H b) (snd es) k) es ->
        sc_exp_inv Γ Γty H b (Emerge (x, tx) es ann) k.
    Proof.
      intros * Hnd Hk Hin Hvar Hes ss Hwt Hwc Hsem; simpl.
      inv Hwt. inv Hwc. inv Hsem.
      assert (length vs = length tys) as Hlen1.
      { eapply Forall2Brs_length1 in H21.
        2:{ simpl_Forall. eapply sem_exp_numstreams; eauto with lclocking. }
        destruct es as [|(?&?)]; try congruence. simpl in *.
        inv H21; simpl in *.
        inv H16. rewrite H11, length_clocksof_annots; auto.
      }
      assert (Hlen2:=H21). eapply Forall2Brs_length2 in Hlen2.
      eapply Forall2Brs_sc_exp_inv1 in H21; eauto.
      2,3:rewrite Hlen1; auto.
      eapply Forall2_forall2 in H22 as (Hlen3&Hmerge).
      eapply sc_merge in Hmerge. 1,3:eauto. 4,5:eauto. 3:simpl in *; congruence.
      - eapply Forall_forall in Hlen2; [|eapply nth_In; rewrite Hlen1; eauto].
        instantiate (1:=[]). instantiate (1:=[]) in Hlen2.
        destruct (nth k vs []), es; simpl in *; congruence.
      - eapply Forall_impl; [|eapply H21]; intros (?&?) ?; simpl.
        rewrite map_nth' with (d':=bool_velus_type); eauto.
    Qed.

    Lemma sc_exp_case : forall Γ Γty H b e es d ann k,
        k < length (fst ann) ->
        sc_exp_inv Γ Γty H b e 0 ->
        Forall (fun es => P_exps (sc_exp_inv Γ Γty H b) (snd es) k) es ->
        LiftO True (fun d => P_exps (sc_exp_inv Γ Γty H b) d k) d ->
        sc_exp_inv Γ Γty H b (Ecase e es d ann) k.
    Proof.
      intros * Hk He Hes Hd ss Hwt Hwc Hsem; simpl.
      inv Hwt; inv Hwc; inv Hsem.
      - assert (length vs = length tys) as Hlen1.
        { eapply Forall2Brs_length1 in H26.
          2:{ simpl_Forall. eapply sem_exp_numstreams; eauto with lclocking. }
          destruct es as [|(?&?)]; try congruence. simpl in *.
          inv H26; simpl in *.
          inv H10. rewrite length_typesof_annots; auto.
        }
        eapply Forall3_forall3 in H27 as (?&?&Hcase).
        eapply ac_case in Hcase. rewrite <-Hcase.
        3:instantiate (2:=[]). 4:instantiate (2:=None). 3-5:reflexivity. 2:rewrite Hlen1; auto.
        eapply He in H25; eauto.
        rewrite H14 in H25; simpl in H25.
        erewrite map_nth' with (d':=bool_velus_type); eauto.
      - assert (length vs = length (typesof d0)) as Hlen1.
        { eapply Forall2Brs_length1 in H29.
          2:{ simpl_Forall. eapply sem_exp_numstreams; eauto with lclocking. }
          destruct es as [|(?&?)]; try congruence. simpl in *.
          inv H29; simpl in *.
          inv H11. rewrite <-H13, length_typesof_annots; auto.
        }
        eapply Forall3_forall3 in H31 as (?&?&Hcase).
        eapply ac_case in Hcase. rewrite <-Hcase.
        3:instantiate (2:=[]). 4:instantiate (2:=None). 3-5:reflexivity. 2:rewrite Hlen1; auto.
        eapply He in H24; eauto.
        rewrite H16 in H24; simpl in H24.
        erewrite map_nth' with (d':=bool_velus_type); eauto.
    Qed.

    Lemma sem_exp_sem_var :
      forall Γ H b e vs,
        wc_exp G Γ e ->
        sem_exp G H b e vs ->
        Forall2 (fun '(_, o) s => LiftO True (fun x : ident => sem_var (fst H) x s) o) (nclockof e) vs.
    Proof.
      intros * Hwc Hsem.
      assert (length vs = length (nclockof e)) as Hlen.
      { rewrite length_nclockof_numstreams. eapply sem_exp_numstreams; eauto with lclocking. }
      inv Hwc; inv Hsem; simpl in *; repeat constructor; repeat rewrite map_length in *.
      - (* var *)
        simpl; auto.
      - (* fby *)
        apply Forall2_map_1, Forall2_forall; split; auto; intros.
        simpl; auto.
      - (* arrow *)
        apply Forall2_map_1, Forall2_forall; split; auto; intros.
        simpl; auto.
      - (* when *)
        apply Forall2_map_1, Forall2_forall; split; auto; intros.
        simpl; auto.
      - (* merge *)
        apply Forall2_map_1, Forall2_forall; split; auto; intros.
        simpl; auto.
      - (* case *)
        apply Forall2_map_1, Forall2_forall; split; auto; intros.
        simpl; auto.
      - (* case *)
        apply Forall2_map_1, Forall2_forall; split; auto; intros.
        simpl; auto.
      - (* app *)
        apply Forall2_map_1, Forall2_forall; split; auto; intros.
        simpl; auto.
    Qed.

    Corollary sem_exps_sem_var :
      forall Γ H b es vs,
        Forall (wc_exp G Γ) es ->
        Forall2 (sem_exp G H b) es vs ->
        Forall2 (fun '(_, o) s => LiftO True (fun x : ident => sem_var (fst H) x s) o) (nclocksof es) (concat vs).
    Proof.
      induction es; intros * Hwc Hsem; inv Hwc; inv Hsem; simpl; auto.
      apply Forall2_app; auto.
      eapply sem_exp_sem_var; eauto.
    Qed.

    Lemma sc_exp_app : forall Γ Γty H b f es er ann k,
        wc_global G ->
        k < length ann ->
        (forall k0 : nat, k0 < length (annots es) -> P_exps (sc_exp_inv Γ Γty H b) es k0) ->
        sc_exp_inv Γ Γty H b (Eapp f es er ann) k.
    Proof.
      intros * HwcG Hlen Hk' ? Hwt Hwc Hsem; simpl.

      assert (length ss = length ann0) as Hlen'.
      { eapply sem_exp_numstreams in Hsem; eauto with lclocking. }

      inv Hwt. inv Hwc. inv Hsem.
      eapply wc_find_node in HwcG as (G'&Wcn); eauto.
      assert (Wcn':=Wcn). destruct Wcn' as (WcIn&WcInOut&_).
      rewrite H6 in H13; inv H13.

      (* Arguments *)
      assert (Hse:=H11). eapply P_exps_sc_exp_inv_all in Hse; eauto.

      (* Returning aligned values *)
      assert (Hvars:=H11).
      eapply sem_exps_sem_var, sc_outside_mask with (ncks:=map (fun '(_, ck) => (ck, None)) ann0) in Hvars; eauto.
      - eapply Forall2_forall2 in Hvars as [? Hck].
        repeat rewrite map_length in *.
        specialize (Hck Cbase (abstract_clock (def_stream b)) _ _ _ Hlen eq_refl eq_refl).
        rewrite map_nth, map_map in Hck; eauto.
        erewrite map_ext; eauto. intros (?&?); auto.
      - apply Forall2_map_1, Forall2_forall; split; auto; intros (?&?); simpl; auto.
      - (* Returning aligned values *)
        intros k'.
        specialize (H24 k'). inv H24. rewrite H1 in H6; inv H6.
        exists H0. repeat split; eauto.
        eapply sc_inside_mask in WcIn. 3-5:eauto. 2:eauto.
        eapply Hscnodes in H1; eauto. econstructor; eauto.
    Qed.

    Lemma sc_exp' : forall Γ Γty H b e k,
        NoDupMembers Γ ->
        wc_global G ->
        wt_exp G Γty e ->
        wc_exp G Γ e ->
        k < numstreams e ->
        (forall cx, Is_free_left Γ cx k e -> sc_var_inv Γ H b cx) ->
        sc_exp_inv Γ Γty H b e k.
    Proof.
      intros * Hnd1 Hsc Hwt Hwc Hnum Hfree.
      eapply exp_causal_ind with (Γ:=Γ) (P_exp:=sc_exp_inv _ _ H b); eauto with lclocking; intros.
      - apply sc_exp_const.
      - apply sc_exp_enum.
      - eapply sc_exp_var; eauto.
      - eapply sc_exp_last; eauto.
      - apply sc_exp_unop; auto.
      - apply sc_exp_binop; auto.
      - apply sc_exp_fby; auto.
      - apply sc_exp_arrow; auto.
      - eapply sc_exp_when; eauto.
      - eapply sc_exp_merge; eauto.
      - apply sc_exp_case; auto.
      - eapply sc_exp_app; eauto.
    Qed.

    Lemma sc_exp_equation : forall Γ Γty H b xs es k cx,
        wc_global G ->
        NoDup (map snd (idcaus_of_senv Γ)) ->
        NoDupMembers Γ ->
        k < length xs ->
        wt_equation G Γty (xs, es) ->
        wc_equation G Γ (xs, es) ->
        Sem.sem_equation G H b (xs, es) ->
        (forall cx, Is_free_left_list Γ cx k es -> sc_var_inv Γ H b cx) ->
        HasCaus Γ (nth k xs xH) cx ->
        sc_var_inv Γ H b cx.
    Proof.
      intros * HwcG Hnd1 Hnd2 Hk Hwt Hwc Hsem Hexps Hin. split; intros ???? Hin' Hvar.
      2:{ exfalso. simpl_In.
          eapply NoDup_HasCaus_HasLastCaus; eauto. }
      inv Hwt. inv Hsem.
      assert (x = nth k xs xH).
      { eapply HasCaus_snd_det; eauto. } subst.
      assert (xs0 ≡ nth k (concat ss) (def_stream b)) as Hequiv.
      { eapply Forall2_forall2 in H9 as [_ Hvar'].
        specialize (Hvar' xH (def_stream b) _ _ _ Hk eq_refl eq_refl).
        eapply sem_var_det in Hvar'; eauto. }
      rewrite Hequiv; auto.
      inv Hwc.
      - (* app *)
        assert (nth k (map snd anns) Cbase = ck); subst; auto.
        { eapply Forall2_forall2 in H13 as [_ HIn'].
          specialize (HIn' xH Cbase _ _ _ Hk eq_refl eq_refl).
          inv Hin'. inv HIn'.
          eapply NoDupMembers_det in H3; eauto; subst. auto. }

        simpl_Forall. rename H4 into Hsem.
        assert (length y = length anns) as Hlen'.
        { eapply sem_exp_numstreams in Hsem; eauto with ltyping. }

        inv H14. inv Hsem.
        assert (HwcG':=HwcG). eapply wc_find_node in HwcG' as (G'&Wcn); eauto.
        assert (Wcn':=Wcn). destruct Wcn' as (WcIn&WcInOut&_).
        rewrite H7 in H17; inv H17.

        (* Arguments *)
        assert (Hse:=H24). eapply P_exps_sc_exp_inv_all in Hse; eauto.
        2:{ intros.
            eapply Pexp_Pexps; eauto.
            - simpl_Forall. eapply sc_exp'; eauto.
            - intros ??. eapply Hexps.
              left; simpl. 2:constructor.
              1,2:(apply Forall2_length in H13; setoid_rewrite <-H13; auto).
              left.
              eapply Is_free_left_list_Exists; eauto.
        }

        (* Returning aligned values *)
        simpl in *. rewrite app_nil_r in *.
        assert (Hvars:=H24).
        eapply sem_exps_sem_var, sc_outside_mask with (ncks:=map (fun '(ck, x) => (ck, Some x)) (combine (map snd anns) xs)) in Hvars; eauto.
        + eapply Forall2_forall2 in Hvars as [? Hck].
          repeat rewrite map_length in *.
          assert (k < length (combine (map snd anns) xs)) as Hlen2.
          { apply Forall2_length in H2. rewrite combine_length, H2, 2 map_length, Nat.min_id.
            now erewrite <-map_length, <-H2. }
          specialize (Hck Cbase (abstract_clock (def_stream b)) _ _ _ Hlen2 eq_refl eq_refl).
          erewrite map_nth, map_map, map_ext, combine_map_fst' in Hck; eauto.
          1:eapply Forall2_length in H2; rewrite H2, 2 map_length; eauto.
          intros (?&?); auto.
        + apply Forall2_map_1, Forall3_combine'1, Forall3_ignore1'.
          { apply Forall2_length in H13; auto. rewrite map_length; auto. }
          eapply Forall2_impl_In; [|eauto]; intros; simpl in *; auto.
        + simpl_Forall; eauto.
        + eapply Forall2_map_2, Forall3_combine'2; eauto.
        + (* Returning aligned values *)
          intros k'.
          specialize (H28 k'). inv H28. rewrite H3 in H7; inv H7.
          exists H1. repeat split; eauto.
          eapply sc_inside_mask in WcIn. 3-5:eauto. 2:eauto.
          eapply Hscnodes in Wcn; eauto. econstructor; eauto. simpl_Forall; eauto.
      - assert (nth k (clocksof es) Cbase = ck); subst; auto.
        { eapply Forall2_forall2 in H6 as [_ HIn'].
          specialize (HIn' xH Cbase _ _ _ Hk eq_refl eq_refl).
          inv Hin'. inv HIn'. eapply NoDupMembers_det in H3; eauto; subst. auto.
        }
        assert (P_exps (sc_exp_inv Γ Γty H b) es k) as Hexps'.
        { eapply Pexp_Pexps; eauto.
          - simpl_Forall. eapply sc_exp'; eauto.
          - eapply Forall2_length in H2. rewrite length_typesof_annots in H2. congruence.
        }

        eapply P_exps_sc_exp_inv in Hexps'; eauto.
    Qed.

    Lemma sem_var_refines_iff : forall dom H H' x v,
        Env.refines (@EqSt _) H H' ->
        Env.dom_lb H dom ->
        In x dom ->
        sem_var H x v <-> sem_var H' x v.
    Proof.
      intros * Href Hdom Hin; split; intros Hvar.
      - eapply sem_var_refines; eauto.
      - eapply sem_var_refines''; eauto.
    Qed.

    Lemma sem_clock_refines_iff : forall H H' ck bs bs',
        Env.refines (@EqSt _) H H' ->
        (forall x, Is_free_in_clock x ck -> Env.In x H' -> Env.In x H) ->
        sem_clock H bs ck bs' <-> sem_clock H' bs ck bs'.
    Proof with eauto with lcsem.
      intros * Href Hin. split. eapply sem_clock_refines; eauto.
      revert ck bs bs' H H' Href Hin.
      induction ck; intros * Href Hin Hsem; inv Hsem.
      - constructor; auto.
      - econstructor; eauto.
        + eapply IHck; eauto.
          intros * Hf. apply Hin; constructor; auto.
        + eapply sem_var_refines'; eauto.
          apply Hin; eauto using sem_var_In. constructor.
    Qed.

    (** ** more `mask` properties *)

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

    Lemma history_mask_count : forall r H n,
        Env.Equiv eq (CIStr.tr_history (mask_hist (count r) # n r H) n) (CIStr.tr_history H n).
    Proof.
      intros *.
      rewrite Env.Equiv_orel. intros ?.
      unfold mask_hist in *.
      destruct (Env.find x (CIStr.tr_history H n)) eqn:Hfind.
      1,2:(repeat setoid_rewrite Env.Props.P.F.map_o in Hfind;
           repeat setoid_rewrite Env.Props.P.F.map_o).
      - apply option_map_inv in Hfind as (?&Hfind&?); subst.
        rewrite Hfind; simpl.
        unfold tr_Stream; rewrite maskv_nth, Nat.eqb_refl; auto with datatypes.
      - apply option_map_inv_None in Hfind. rewrite Hfind; simpl; auto with datatypes.
    Qed.

    Corollary sem_var_instant_mask_hist_count: forall H n r x v,
        IStr.sem_var_instant (CIStr.tr_history H n) x v <->
        IStr.sem_var_instant (CIStr.tr_history (mask_hist ((count r) # n) r H) n) x v.
    Proof.
      intros.
      split; intros; eapply IStr.sem_var_instant_morph; eauto.
      symmetry. 1,2:eapply history_mask_count.
    Qed.

    Corollary sem_var_unmask: forall r H x v,
        (forall k, sem_var (mask_hist k r H) x (maskv k r v)) ->
        sem_var H x v.
    Proof.
      intros * Hsem.
      specialize (Hsem 0) as Hsem0. inv Hsem0.
      apply Env.Props.P.F.map_mapsto_iff in H1 as (?&?&Hfind); subst.
      econstructor; eauto.
      apply ntheq_eqst. intros n.
      specialize (Hsem ((count r) # n)). inv Hsem.
      apply Env.Props.P.F.map_mapsto_iff in H1 as (?&?&Hfind'); subst.
      unfold Env.MapsTo in *. rewrite Hfind in Hfind'; inv Hfind'.
      apply eqst_ntheq with (n:=n) in H3. rewrite 2 maskv_nth, Nat.eqb_refl in H3; auto.
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

    Lemma sc_var_inv_mask : forall Γ H b x r k,
        sc_var_inv Γ H b x ->
        sc_var_inv Γ (Sem.mask_hist k r H) (maskb k r b) x.
    Proof.
      intros * Hinv.
      split; intros ???? Hin Hvar;
        [destruct Hinv as (Hinv&_)|destruct Hinv as (_&Hinv)];
        eapply sem_var_mask_inv in Hvar as (?&Hvar&Heq);
        rewrite Heq, ac_mask;
        eapply sem_clock_mask;
        eapply Hinv; eauto.
    Qed.

    Lemma sc_var_inv_unmask : forall Γ H b x r,
      (forall k : nat, sc_var_inv Γ (Sem.mask_hist k r H) (maskb k r b) x) ->
      sc_var_inv Γ H b x.
    Proof.
      intros * Hinv. split; intros ???? Hin Hvar.
      1,2:(eapply sem_clock_unmask with (r:=r); intros k;
           specialize (Hinv k)).
      destruct Hinv as (Hinv&_). 2:destruct Hinv as (_&Hinv).
      1,2:(rewrite <-ac_mask; eapply Hinv; eauto;
           eapply sem_var_mask; eauto).
    Qed.

    (** ** more `filter` properties *)

    Lemma sem_clock_filter : forall Hi Hi' bs ck k sc,
        sem_clock Hi bs ck (abstract_clock sc) ->
        sem_clock Hi' (ffilterb k sc bs) Cbase (ffilterb k sc (abstract_clock sc)).
      Proof.
        intros * Hsemck.
        constructor.
        eapply ntheq_eqst. intros. rewrite 2 ffilterb_nth, ac_nth.
        destruct (_ ==b _) eqn:Heqsc; auto.
        apply svalue_eqb_eq in Heqsc. setoid_rewrite Heqsc.
        eapply sem_clock_equiv in Hsemck. specialize (Hsemck n). repeat rewrite tr_Stream_nth in Hsemck.
        setoid_rewrite ac_nth in Hsemck. setoid_rewrite Heqsc in Hsemck. apply IStr.sem_clock_instant_true_inv in Hsemck; auto.
      Qed.

    Lemma sem_clock_select : forall Hi Hi' bs ck e k sc,
        sem_clock Hi bs ck (abstract_clock sc) ->
        sem_clock Hi' (fselectb e k sc bs) Cbase (fselectb e k sc (abstract_clock sc)).
      Proof.
        intros * Hsemck.
        constructor.
        eapply ntheq_eqst. intros. setoid_rewrite maskb_nth. rewrite 2 ffilterb_nth, ac_nth.
        destruct (_ ==b _) eqn:Heqsc, (_ =? _); auto.
        apply svalue_eqb_eq in Heqsc. setoid_rewrite Str_nth_map in Heqsc.
        destruct (sc # n) as [|(?&?)] eqn:Hscn; simpl in *; try congruence.
        eapply sem_clock_equiv in Hsemck. specialize (Hsemck n). repeat rewrite tr_Stream_nth in Hsemck.
        setoid_rewrite ac_nth in Hsemck. setoid_rewrite Hscn in Hsemck.
        apply IStr.sem_clock_instant_true_inv in Hsemck; auto.
      Qed.

    Section sem_block_ck'.

      Section sem_scope.

        Context {A : Type}.

        Variable sem_block : Sem.history -> A -> Prop.

        Inductive sem_scope_ck' (envS : list ident) : Sem.history -> Stream bool -> (scope A) -> Prop :=
        | Sckscope : forall Hi Hi' Hl Hl' bs locs blks,
            (forall x vs, sem_var Hi' x vs -> ~InMembers x locs -> sem_var Hi x vs) ->

            Env.refines (@EqSt _) Hl Hl' ->
            (forall x ty ck cx e0 clx,
                In (x, (ty, ck, cx, Some (e0, clx))) locs ->
                exists vs0 vs1 vs,
                  sem_exp G (Hi', Hl') bs e0 [vs0] /\ sem_var Hi' x vs1 /\ fby vs0 vs1 vs /\ sem_var Hl' x vs) ->

            sem_block (Hi', Hl') blks ->

            Forall (fun x => sc_var_inv (senv_of_locs locs) (Env.union Hi Hi', Hl') bs x) envS ->
            sem_scope_ck' envS (Hi, Hl) bs (Scope locs blks).
      End sem_scope.

      Inductive sem_block_ck' (envP : list ident) : Sem.history -> Stream bool -> block -> Prop :=
      | Sckbeq : forall Hi bs eq,
          sem_equation G Hi bs eq ->
          sem_block_ck' envP Hi bs (Beq eq)
      | Sckreset : forall Hi bs blocks er sr r,
          sem_exp G Hi bs er [sr] ->
          bools_of sr r ->
          (forall k, Forall (sem_block_ck' envP (Sem.mask_hist k r Hi) (maskb k r bs)) blocks) ->
          sem_block_ck' envP Hi bs (Breset blocks er)
      | Sckswitch:
        forall Hi b ec branches sc,
          sem_exp G Hi b ec [sc] ->
          wt_streams [sc] (typeof ec) ->
          Forall (fun blks =>
                    exists Hi', Sem.filter_hist (fst blks) sc Hi Hi'
                           /\ let bi := ffilterb (fst blks) sc b in
                             sem_scope_ck'  (fun Hi' => Forall (sem_block_ck' envP Hi' bi)) envP Hi' bi (snd blks)) branches ->
          sem_block_ck' envP Hi b (Bswitch ec branches)
      | Sckauto:
        forall H bs ini oth states ck bs' stres0 stres1 stres,
          sem_clock (fst H) bs ck bs' ->
          sem_transitions G H bs' (List.map (fun '(e, t) => (e, (t, false))) ini) (oth, false) stres0 ->
          fby stres0 stres1 stres ->
          Forall (fun state =>
                    forall k, exists Hik, Sem.select_hist (fst state) k stres H Hik
                                /\ let bik := fselectb (fst state) k stres bs in
                                  sem_scope_ck' (fun Hi' blks =>
                                                   Forall (sem_block_ck' envP Hi' bik) (fst blks)
                                                   /\ sem_transitions G Hi' bik (snd blks) (fst state, false) (fselect absent (fst state) k stres stres1)
                                                ) envP Hik bik (snd state)
                 ) states ->
          sem_block_ck' envP H bs (Bauto ck (ini, oth) states)
      | Scklocal:
        forall Hi bs scope,
          sem_scope_ck' (fun Hi' => Forall (sem_block_ck' envP Hi' bs)) envP Hi bs scope ->
          sem_block_ck' envP Hi bs (Blocal scope).

      Lemma sem_block_sem_block_ck' : forall blk Hi bs,
          sem_block G Hi bs blk ->
          sem_block_ck' [] Hi bs blk.
      Proof.
        induction blk using block_ind2; intros * Hsem; inv Hsem.
        - (* equation *)
          constructor; auto.
        - (* reset *)
          econstructor; eauto.
          intros k. specialize (H7 k).
          simpl_Forall; eauto.
        - (* switch *)
          econstructor; eauto.
          simpl_Forall; do 2 esplit; eauto.
          inv H3; econstructor; eauto. simpl_Forall; eauto.
        - (* automaton *)
          econstructor; eauto.
          simpl_Forall. specialize (H9 k); destruct_conjs.
          do 2 esplit; eauto.
          inv H2; econstructor; eauto. destruct_conjs; split; simpl_Forall; eauto.
        - (* locals *)
          constructor.
          inv H3; econstructor; eauto.
          simpl_Forall; eauto.
      Qed.

      Lemma sem_block_ck'_sem_block : forall envP blk Hi bs,
          sem_block_ck' envP Hi bs blk ->
          sem_block G Hi bs blk.
      Proof.
        induction blk using block_ind2; intros * Hsem; inv Hsem.
        - (* equation *)
          constructor; auto.
        - (* reset *)
          econstructor; eauto.
          intros k. specialize (H6 k).
          simpl_Forall; eauto.
        - (* switch *)
          econstructor; eauto.
          simpl_Forall; do 2 esplit; simpl_Forall; eauto.
          inv H3; econstructor; eauto. simpl_Forall; eauto.
        - (* automaton *)
          econstructor; eauto.
          simpl_Forall. specialize (H9 k); destruct_conjs.
          do 2 esplit; eauto.
          inv H2; econstructor; eauto. destruct_conjs; split; simpl_Forall; eauto.
        - (* locals *)
          constructor.
          inv H3. econstructor; eauto.
          simpl_Forall; eauto.
      Qed.

      Lemma sem_block_ck'_Perm : forall xs ys blk Hi bs,
          Permutation xs ys ->
          sem_block_ck' xs Hi bs blk ->
          sem_block_ck' ys Hi bs blk.
      Proof.
        induction blk using block_ind2; intros * Hperm Hsem;
          inv Hsem.
        - (* equation *)
          constructor; auto.
        - (* reset *)
          econstructor; eauto.
          intros k. specialize (H6 k).
          simpl_Forall; eauto.
        - (* switch *)
          econstructor; eauto.
          simpl_Forall; do 2 esplit; eauto.
          inv H3; econstructor; eauto.
          simpl_Forall; eauto.
          setoid_rewrite <-Hperm; auto.
        - (* automaton *)
          econstructor; eauto.
          simpl_Forall. specialize (H9 k); destruct_conjs.
          do 2 esplit; eauto. inv H2; destruct_conjs. econstructor; eauto.
          split; simpl_Forall; eauto.
          setoid_rewrite <-Hperm; auto.
        - (* local *)
          constructor.
          inv H3. econstructor; eauto.
          simpl_Forall; eauto.
          setoid_rewrite <-Hperm; auto.
      Qed.

      Global Add Parametric Morphism envP : (sem_block_ck' envP)
          with signature (history_equiv ==> eq ==> eq ==> Basics.impl)
            as sem_block_ck'_Equiv.
      Proof.
        intros Hi1 Hi2 HH bs blk. revert Hi1 Hi2 HH bs.
        induction blk using block_ind2; intros * HH * Hsem; inv Hsem.
        - (* equation *)
          constructor. now rewrite <-HH.
        - (* reset *)
          econstructor; eauto.
          + now rewrite <-HH.
          + intros k. specialize (H6 k).
            simpl_Forall; eauto.
            eapply H; eauto.
            destruct HH as (HH1&HH2); split; unfold Sem.mask_hist.
            now rewrite <-HH1. now rewrite <-HH2.
        - (* switch *)
          econstructor; eauto.
          + now rewrite <-HH.
          + simpl_Forall; do 2 esplit; eauto.
            destruct HH as (HH1&HH2), H1. split.
            * now rewrite <-HH1.
            * now rewrite <-HH2.
        - (* automaton *)
          econstructor; eauto.
          + destruct HH as (HH1&HH2). rewrite <-HH1; eauto.
          + now rewrite <-HH.
          + simpl_Forall. specialize (H9 k); destruct_conjs.
            do 2 esplit; eauto.
            destruct HH as (HH1&HH2), H1. split.
            * now rewrite <-HH1.
            * now rewrite <-HH2.
        - (* locals *)
          destruct Hi2. constructor.
          inv H3; econstructor. 3,4:eauto.
          + intros. destruct HH as (HH&_). rewrite <-HH. eapply H2; eauto.
          + destruct HH as (_&HH). rewrite <-HH; eauto.
          + simpl_Forall. destruct HH as (HH1&HH2). destruct H9.
            split; simpl in *; intros; rewrite <-HH1 in *; eauto.
      Qed.

      Lemma sem_scope_ck'_refines {A} P_vd P_nd P_sem : forall envP locs (blk: A) xs H H' Hl bs,
          VarsDefinedScope P_vd (Scope locs blk) xs ->
          NoDupScope P_nd xs (Scope locs blk) ->
          Env.refines (@EqSt _) H H' ->
          sem_scope_ck' P_sem envP (H, Hl) bs (Scope locs blk) ->
          (forall xs Γ Hi,
            incl xs Γ ->
            P_vd blk xs ->
            P_nd Γ blk ->
            P_sem Hi blk ->
            Env.dom_lb (fst Hi) xs) ->
          (forall xs Hi Hi' Hl,
              P_vd blk xs ->
              P_nd xs blk ->
              Env.refines (@EqSt _) Hi Hi' ->
              P_sem (Hi, Hl) blk ->
              P_sem (Hi', Hl) blk) ->
          sem_scope_ck' P_sem envP (H', Hl) bs (Scope locs blk).
      Proof.
        intros * Hvd Hnd Href Hsem Hdoml Hind; inv Hvd; inv Hnd; inv Hsem.
        econstructor; [|eauto|eauto|eauto|eauto]; eauto using sem_var_refines.
        assert (Env.refines (EqSt (A:=svalue)) (Env.union H Hi') (Env.union H' Hi')) as Href'.
        { intros ?? Hfind.
          eapply Env.union_find4' in Hfind as [(Hfind1&Hfind2)|Hfind2].
          * eapply Href in Hfind1 as (v'&?&?). exists v'; split; auto.
            eapply Env.union_find2; eauto.
          * exists v. split; try reflexivity. eapply Env.union_find3'; eauto. }
        eapply Forall_impl; [|eauto]; intros ? (Hsc1&Hsc2); simpl in *.
        split; intros ???? Hin Hv.
        1,2:eapply sem_clock_refines; eauto. eapply Hsc1; eauto; simpl in *.
        assert (Env.dom_lb Hi' (map fst locs)) as Hdom.
        { eapply Env.dom_lb_incl. 2:eapply Hdoml in H12; eauto.
          1,2:solve_incl_app. }
        inv Hin. simpl_In.
        eapply sem_var_refines''; eauto using Env.union_dom_lb2.
        solve_In.
      Qed.

      Lemma sem_block_ck'_refines : forall envP blk xs H H' Hl bs,
          VarsDefined blk xs ->
          NoDupLocals xs blk ->
          Env.refines (@EqSt _) H H' ->
          sem_block_ck' envP (H, Hl) bs blk ->
          sem_block_ck' envP (H', Hl) bs blk.
      Proof.
        induction blk using block_ind2; intros * Hvars Hnd Href Hsem;
          inv Hvars; inv Hnd; inv Hsem.
        - (* equation *)
          constructor; eauto using Sem.sem_equation_refines.
        - (* reset *)
          econstructor; eauto using Sem.sem_exp_refines.
          intros k. specialize (H9 k).
          rewrite Forall_forall in *; intros; eauto.
          eapply Forall2_ignore2, Forall_forall in H4 as (?&?&?); eauto.
          eapply H. 1-3,5:eauto.
          + eapply NoDupLocals_incl; eauto. eapply incl_concat; eauto.
          + eapply Env.refines_map; eauto. intros ?? Heq. now rewrite Heq.
        - (* switch *)
          econstructor; eauto using Sem.sem_exp_refines.
          simpl_Forall. do 2 esplit; eauto.
          destruct H2; split; auto.
          intros ?? Hfind. apply H2 in Hfind as (?&Heq1&Hfind). apply Href in Hfind as (?&Heq2&Hfind).
          do 2 esplit; [|eauto]. rewrite <-Heq2; auto.
        - (* automaton *)
          econstructor; eauto using sem_clock_refines, Sem.sem_transitions_refines.
          simpl_Forall. specialize (H13 k); destruct_conjs.
          do 2 esplit; eauto.
          destruct H2 as (Hsel1&?); split; auto.
          intros ?? Hfind. apply Hsel1 in Hfind as (?&Heq1&Hfind). apply Href in Hfind as (?&Heq2&Hfind).
          do 2 esplit; [|eauto]. rewrite <-Heq2; auto.
        - (* locals *)
          constructor.
          eapply sem_scope_ck'_refines; eauto.
          1,2:intros; simpl in *; simpl_Forall; inv_VarsDefined; eauto.
          + destruct Hi.
            eapply Forall_sem_block_dom_lb; eauto;
              simpl_Forall; eauto using NoDupLocals_incl, sem_block_ck'_sem_block.
          + eapply H; eauto.
            eapply NoDupLocals_incl; [|eauto]. rewrite <-H9; eauto using incl_concat.
      Qed.

      Corollary sem_scope_ck'_refines1 : forall envP locs blk Γ xs H H' Hl bs,
          incl xs Γ ->
          VarsDefinedScope (fun blks ys => exists xs : list (list ident), Forall2 VarsDefined blks xs /\ Permutation (concat xs) ys) (Scope locs blk) xs ->
          NoDupScope (fun Γ => Forall (NoDupLocals Γ)) Γ (Scope locs blk) ->
          Env.refines (@EqSt _) H H' ->
          sem_scope_ck' (fun Hi => Forall (sem_block_ck' envP Hi bs)) envP (H, Hl) bs (Scope locs blk) ->
          sem_scope_ck' (fun Hi => Forall (sem_block_ck' envP Hi bs)) envP (H', Hl) bs (Scope locs blk).
      Proof.
        intros * Hincl Hdef Hnd Href Hsem.
        eapply sem_scope_ck'_refines; eauto.
        - eapply NoDupScope_incl; eauto.
          intros; simpl in *; simpl_Forall; eauto using NoDupLocals_incl.
        - intros; simpl in *. inv_VarsDefined.
          destruct Hi.
          eapply Forall_sem_block_dom_lb; eauto;
            simpl_Forall; eauto using NoDupLocals_incl, sem_block_ck'_sem_block.
        - intros; simpl in *; simpl_Forall. inv_VarsDefined.
          eapply sem_block_ck'_refines; eauto.
          eapply NoDupLocals_incl; eauto. rewrite <-H5; eauto using incl_concat.
      Qed.

      Corollary sem_scope_ck'_refines2 : forall envP locs blk Γ xs H H' Hl bs def stres,
          incl xs Γ ->
          VarsDefinedScope (fun blks ys => exists xs : list (list ident), Forall2 VarsDefined (fst blks) xs /\ Permutation (concat xs) ys) (Scope locs blk) xs ->
          NoDupScope (fun Γ blks => Forall (NoDupLocals Γ) (fst blks)) Γ (Scope locs blk) ->
          Env.refines (@EqSt _) H H' ->
          sem_scope_ck' (fun Hi blks => Forall (sem_block_ck' envP Hi bs) (fst blks)
                                     /\ sem_transitions G Hi bs (snd blks) def stres) envP (H, Hl) bs (Scope locs blk) ->
          sem_scope_ck' (fun Hi blks => Forall (sem_block_ck' envP Hi bs) (fst blks)
                                     /\ sem_transitions G Hi bs (snd blks) def stres) envP (H', Hl) bs (Scope locs blk).
      Proof.
        intros * Hincl Hdef Hnd Href Hsem.
        eapply sem_scope_ck'_refines; eauto.
        - eapply NoDupScope_incl; eauto.
          intros; simpl in *; simpl_Forall; eauto using NoDupLocals_incl.
        - intros; simpl in *. inv_VarsDefined.
          destruct Hi.
          eapply Forall_sem_block_dom_lb; eauto;
            simpl_Forall; eauto using NoDupLocals_incl, sem_block_ck'_sem_block.
        - intros; simpl in *.
          destruct_conjs; split; eauto using Sem.sem_transitions_refines.
          simpl_Forall. inv_VarsDefined.
          eapply sem_block_ck'_refines; eauto.
          eapply NoDupLocals_incl; eauto. rewrite <-H5; eauto using incl_concat.
      Qed.

      Lemma sem_scope_ck'_restrict {A} P_vd P_nd P_wc sem_block:
        forall envP Γ xs Hi Hl bs locs (blks : A),
          VarsDefinedScope P_vd (Scope locs blks) xs ->
          NoDupScope P_nd xs (Scope locs blks) ->
          wc_scope P_wc G Γ (Scope locs blks) ->
          sem_scope_ck' sem_block envP (Hi, Hl) bs (Scope locs blks) ->
          (forall xs Γ Hi,
              incl xs Γ ->
              P_vd blks xs ->
              P_nd Γ blks ->
              sem_block Hi blks ->
              Env.dom_lb (fst Hi) xs) ->
          (forall Γ xs Hi Hl,
              P_vd blks xs ->
              P_nd xs blks ->
              P_wc Γ blks ->
              sem_block (Hi, Hl) blks ->
              sem_block (Env.restrict Hi (List.map fst Γ), Hl) blks) ->
          sem_scope_ck' sem_block envP (Env.restrict Hi (List.map fst Γ), Hl) bs (Scope locs blks).
      Proof.
        intros * Hvd Hnd Hwc Hsem Hdomlb Hind; inv Hvd; inv Hnd; inv Hwc; inv Hsem.
        eapply Sckscope with (Hi':=Env.restrict Hi' (List.map fst (Γ ++ senv_of_locs locs))); eauto.
        - intros * Hsem Hnin.
          eapply sem_var_restrict_inv in Hsem as (Hin&Hsem).
          eapply sem_var_restrict; eauto.
          simpl_app. apply in_app_iff in Hin as [Hin|Hin]; auto.
          setoid_rewrite map_fst_senv_of_locs in Hin.
          exfalso. apply Hnin, fst_InMembers; auto.
        - intros * Hin. edestruct H13; eauto. destruct_conjs.
          simpl_Forall.
          do 3 esplit. repeat split; eauto.
          eapply Sem.sem_exp_restrict; eauto with lclocking.
          eapply sem_var_restrict; eauto. simpl_app. apply in_or_app. right. solve_In.
        - rewrite Forall_forall in *. intros * Hinp.
          assert (Env.dom_lb Hi' (map fst locs)) as Hdom2.
          { eapply Env.dom_lb_incl. 2:eapply Hdomlb in H14; eauto.
            1,2:solve_incl_app. }
          assert (Env.refines (@EqSt _)
                              (Env.union (Env.restrict Hi (map fst Γ)) (Env.restrict Hi' (map fst (Γ ++ senv_of_locs locs))))
                              (Env.union Hi Hi')) as Href.
          { intros ?? Hfind.
            eapply Env.union_find4' in Hfind as [(Hfind1&Hfind2)|Hfind2].
            - eapply Env.restrict_find_inv in Hfind1 as (Hin'&Hfind1).
              exists v. split; try reflexivity. eapply Env.union_find2; eauto.
              destruct (Env.find x0 Hi') eqn:Hfind3; eauto.
              eapply Env.restrict_find in Hfind3; try rewrite Hfind2 in Hfind3; try congruence.
              rewrite map_app. apply in_or_app; auto.
            - eapply Env.restrict_find_inv in Hfind2 as (?&?).
              exists v. split; try reflexivity; eauto using Env.union_find3'.
          }
          assert (forall x vs,
                     IsVar (Γ ++ senv_of_locs locs) x ->
                     sem_var (Env.union Hi Hi') x vs ->
                     sem_var (Env.union (Env.restrict Hi (map fst Γ)) (Env.restrict Hi' (map fst (Γ ++ senv_of_locs locs)))) x vs) as Href'.
          { intros ?? Hinm Hvar'. inv Hvar'.
            eapply Env.union_find4' in H0 as [(Hfind1&Hfind2)|Hfind2].
            - inv Hinm. apply InMembers_app in H as [Hinm|Hinm].
              + econstructor; eauto.
                eapply Env.union_find2. eapply Env.restrict_find; eauto. eapply fst_InMembers; eauto.
                eapply Env.restrict_find_None; eauto.
              + exfalso. eapply Env.dom_lb_use in Hdom2 as (?&Hfind3).
                * rewrite Hfind3 in Hfind2. congruence.
                * erewrite InMembers_senv_of_locs, fst_InMembers in Hinm. auto.
            - econstructor; eauto. eapply Env.union_find3', Env.restrict_find; eauto.
              rewrite <-fst_InMembers. now inv Hinm. }
          split; intros ???? Hin Hvar; simpl in *.
          + edestruct H15 as (Hv&_); eauto. eapply sem_var_refines, Hv in Hvar; eauto.
            eapply sem_clock_refines'; [| |eauto]; eauto.
            * inv Hin. eapply wc_clock_wx_clock in H6; eauto. solve_In.
          + edestruct H15 as (_&Hv); eauto. eapply Hv in Hvar; eauto.
            eapply sem_clock_refines'; [| |eauto]; eauto.
            * inv Hin. eapply wc_clock_wx_clock in H6; eauto. solve_In.
      Qed.

      Lemma sem_block_ck'_restrict : forall envP blk xs Γ H Hl bs,
          VarsDefined blk xs ->
          NoDupLocals xs blk ->
          wc_block G Γ blk ->
          sem_block_ck' envP (H, Hl) bs blk ->
          sem_block_ck' envP (Env.restrict H (List.map fst Γ), Hl) bs blk.
      Proof with eauto with lclocking.
        induction blk using block_ind2; intros * Hvars Hnd Hwc Hsem;
          inv Hvars; inv Hnd; inv Hwc; inv Hsem.

        - (* equation *)
          econstructor.
          eapply Sem.sem_equation_restrict...

        - (* reset *)
          econstructor; eauto.
          + eapply Sem.sem_exp_restrict...
          + intros k; specialize (H12 k).
            rewrite Forall_forall in *. intros ? Hin.
            eapply Forall2_ignore2, Forall_forall in H4 as (?&?&?); eauto.
            eapply sem_block_ck'_Equiv; try eapply H; eauto.
            2:{ eapply NoDupLocals_incl; eauto. apply incl_concat; auto. }
            unfold Sem.mask_hist; simpl. split; try reflexivity. now setoid_rewrite <-Env.restrict_map.

        - (* switch *)
          econstructor; eauto.
          + eapply Sem.sem_exp_restrict...
          + simpl_Forall. do 2 esplit.
            2:{ destruct s. eapply sem_scope_ck'_restrict; eauto.
                - intros; simpl in *. destruct_conjs. destruct Hi.
                  eapply Forall_sem_block_dom_lb; eauto.
                  + simpl_Forall; eauto using NoDupLocals_incl.
                  + simpl_Forall; eauto using sem_block_ck'_sem_block.
                - intros; simpl in *. destruct_conjs.
                  simpl_Forall. inv_VarsDefined. eapply H; eauto.
                  eapply NoDupLocals_incl; eauto.
                  take (Permutation _ _) and rewrite <-it. apply incl_concat; auto. }
            destruct H2. split; auto.
            simpl. intros ?? Hfind. apply Env.restrict_find_inv in Hfind as (Hin&Hfind).
            apply H2 in Hfind as (?&Hfilter&Hfind). do 2 esplit; [eauto|eapply Env.restrict_find; eauto].
            simpl_In. edestruct H9 as (Hck&_). 1:econstructor; solve_In; eauto.
            inv Hck. solve_In.

        - (* automaton *)
          econstructor; eauto.
          + eapply Sem.sem_clock_restrict...
          + eapply Sem.sem_transitions_restrict... simpl_Forall.
            eapply wx_exp_incl with (Γ:=Γ'); eauto with lclocking.
            intros * Hv. inv Hv. apply fst_InMembers in H10; simpl_In.
            edestruct H9 as (?&?); eauto with senv.
          + simpl_Forall. specialize (H20 k); destruct_conjs.
            do 2 esplit.
            2:{ destruct s. eapply sem_scope_ck'_restrict; eauto.
                - intros; simpl in *. destruct_conjs. destruct Hi.
                  eapply Forall_sem_block_dom_lb; eauto.
                  + simpl_Forall; eauto using NoDupLocals_incl.
                  + simpl_Forall; eauto using sem_block_ck'_sem_block.
                - intros; simpl in *. destruct_conjs.
                  split.
                  + simpl_Forall. inv_VarsDefined. eapply H; eauto.
                    eapply NoDupLocals_incl; eauto.
                    take (Permutation _ _) and rewrite <-it. apply incl_concat; auto.
                  + eapply Sem.sem_transitions_restrict... simpl_Forall; eauto with lclocking. }
            destruct H2 as (Href1&Href2). split; auto.
            intros ?? Hfind. apply Env.restrict_find_inv in Hfind as (Hin&Hfind).
            eapply Href1 in Hfind as (?&Hfilter&Hfind').
            do 2 esplit; eauto. apply Env.restrict_find; auto.
            simpl_In. edestruct H9 as (?&?); eauto with senv. inv H2. solve_In.

        - (* locals *)
          constructor.
          eapply sem_scope_ck'_restrict; eauto.
          + intros; simpl in *. destruct_conjs. destruct Hi.
            eapply Forall_sem_block_dom_lb; eauto.
            * simpl_Forall; eauto using NoDupLocals_incl.
            * simpl_Forall; eauto using sem_block_ck'_sem_block.
          + intros; simpl in *. destruct_conjs.
            simpl_Forall. inv_VarsDefined. eapply H; eauto.
            eapply NoDupLocals_incl; eauto.
            take (Permutation _ _) and rewrite <-it. apply incl_concat; auto.
      Qed.
    End sem_block_ck'.

    Lemma union_dom_ub_dom_lb_dom {V} : forall (m1 m2 : Env.t V) xs ys,
        Env.dom m1 xs ->
        Env.dom_lb m2 ys ->
        Env.dom_ub m2 (xs ++ ys) ->
        Env.dom (Env.union m1 m2) (xs ++ ys).
    Proof.
      intros * Hdom1 Hdom2 Hdom3.
      eapply Env.dom_intro; intros.
      rewrite Env.union_In, in_app_iff. erewrite Env.dom_use; eauto.
      split; intros [Hin|Hin]; auto.
      - eapply Env.dom_ub_use, in_app_iff in Hdom3; eauto.
      - eapply Env.dom_lb_use in Hin; eauto.
    Qed.

    Lemma sc_var_inv_unfilter : forall Γ Γ' tn sc Hi bs x,
        snd tn > 0 ->
        wt_stream sc (Tenum tn) ->
        (forall y ck, HasCaus Γ y x -> HasClock Γ y ck -> HasCaus Γ' y x /\ HasClock Γ' y Cbase) ->
        (forall y ck, HasCaus Γ y x -> HasClock Γ y ck -> sem_clock (fst Hi) bs ck (abstract_clock sc)) ->
        (forall c, In c (seq 0 (snd tn)) ->
              exists Hi',
                (forall y, HasCaus Γ y x -> Env.In y (fst Hi'))
                /\ Sem.filter_hist c sc Hi Hi'
                /\ sc_var_inv Γ' Hi' (ffilterb c sc bs) x) ->
        (forall y, ~HasLastCaus Γ y x) ->
        sc_var_inv Γ Hi bs x.
    Proof.
      intros * Hn Hwt Hwc Hsck Hsc Hnin.
      split; intros ??? Hca Hck Hv.
      - assert (sem_clock (fst Hi) bs ck (abstract_clock sc)) as Hsemck by eauto.
        assert (abstract_clock sc ≡ abstract_clock xs) as Heq; [|rewrite <-Heq; eauto].
        apply ntheq_eqst. intros n.
        rewrite 2 ac_nth.
        apply SForall_forall with (n:=n) in Hwt.
        destruct (sc # n) eqn:Hscn. simpl in *.
        + edestruct Hsc with (c:=0) as ((Hi'&?)&Hin&(Hfilter&_)&(Hsc'&_)). apply in_seq; lia.
          assert (exists vs, sem_var Hi' x0 vs) as (?&Hv').
          { edestruct Hin as (?&?); eauto. do 2 esplit; eauto. reflexivity. }
          eapply sem_var_filter_inv in Hv' as (?&?&Hfilter'); eauto.
          eapply sem_var_det in Hv; eauto. rewrite <-Hv.
          eapply filter_nth with (n:=n) in Hfilter' as [(?&Heq&?)|[(?&?)|(?&?&?)]]; try congruence.
          setoid_rewrite Heq. setoid_rewrite H0; auto.
        + inv Hwt. edestruct Hsc with (c:=v0) as ((Hi'&?)&Hin&(Hfilter&_)&(Hsc'&_)). apply in_seq; lia.
          assert (exists vs, sem_var Hi' x0 vs) as (?&Hv').
          { edestruct Hin as (?&?); eauto. do 2 esplit; eauto. reflexivity. }
          assert (Hvx:=Hv'). eapply sem_var_filter_inv in Hvx as (?&?&Hfilter'); eauto.
          eapply sem_var_det in Hv; eauto. rewrite <-Hv.
          edestruct Hwc as (Hca'&Hck'); eauto. eapply Hsc' in Hv'; eauto.
          eapply sem_clock_equiv in Hsemck. specialize (Hsemck n). rewrite 2 tr_Stream_nth, ac_nth in Hsemck.
          eapply sem_clock_equiv in Hv'. specialize (Hv' n). rewrite 2 tr_Stream_nth, ac_nth, ffilterb_nth in Hv'.
          eapply filter_nth with (n:=n) in Hfilter' as [(?&?&?)|[(Heq1&Heq2)|(Heq1&Heq2&Heq3&Heq4)]]; try congruence.
          * setoid_rewrite Heq1 in Hsemck. apply IStr.sem_clock_instant_true_inv in Hsemck.
            rewrite Hsemck, Heq1, equiv_decb_refl in Hv'. setoid_rewrite Heq2.
            inv Hv'. setoid_rewrite Heq1; auto.
      - exfalso. eapply Hnin; eauto.
    Qed.

    Lemma sc_var_inv_unselect : forall Γ Γ' tn sc Hi bs x,
        tn > 0 ->
        SForall (fun v => match v with present (e, _) => e < tn | _ => True end) sc ->
        (forall y ck, HasCaus Γ y x -> HasClock Γ y ck -> HasCaus Γ' y x /\ HasClock Γ' y Cbase) ->
        (forall y ck, HasCaus Γ y x -> HasClock Γ y ck -> sem_clock (fst Hi) bs ck (abstract_clock sc)) ->
        (forall c k, In c (seq 0 tn) ->
                exists Hi',
                  (forall y, HasCaus Γ y x -> Env.In y (fst Hi'))
                  /\ Sem.select_hist c k sc Hi Hi'
                  /\ sc_var_inv Γ' Hi' (fselectb c k sc bs) x) ->
        (forall y, ~HasLastCaus Γ y x) ->
        sc_var_inv Γ Hi bs x.
    Proof.
      intros * Hn Hwt Hwc Hsck Hsc Hnin.
      split; intros ??? Hca Hck Hv.
      - assert (sem_clock (fst Hi) bs ck (abstract_clock sc)) as Hsemck by eauto.
        assert (abstract_clock sc ≡ abstract_clock xs) as Heq; [|rewrite <-Heq; eauto].
        apply ntheq_eqst. intros n.
        rewrite 2 ac_nth.
        apply SForall_forall with (n:=n) in Hwt.
        destruct (sc # n) as [|(?&?)] eqn:Hscn. simpl in *.
        + edestruct Hsc with (c:=0) as ((Hi'&?)&Hin&(Hfilter&_)&(Hsc'&_)). apply in_seq; lia.
          assert (exists vs, sem_var Hi' x0 vs) as (?&Hv').
          { edestruct Hin as (?&?); eauto. do 2 esplit; eauto. reflexivity. }
          eapply sem_var_select_inv with (k:=(count (ffilterb 0 (stres_st sc) (stres_res sc))) # n) in Hv' as (?&?&Hfilter'); eauto.
          eapply sem_var_det in Hv; eauto. rewrite <-Hv.
          inv Hfilter'.
          eapply filter_nth with (n:=n) in H0 as [(?&Hx&?)|[(Hscn'&Hx)|(?&Hscn'&?&Hy)]]; try rewrite Hx; auto.
          1,2:setoid_rewrite Str_nth_map in Hscn'; setoid_rewrite Hscn in Hscn'; congruence.
        + edestruct Hsc with (c:=n0) as ((Hi'&?)&Hin&(Hfilter&_)&(Hsc'&_)). apply in_seq; lia.
          assert (exists vs, sem_var Hi' x0 vs) as (?&Hv').
          { edestruct Hin as (?&?); eauto. do 2 esplit; eauto. reflexivity. }
          assert (Hvx:=Hv'). eapply sem_var_select_inv with (k:=(count (ffilterb n0 (stres_st sc) (stres_res sc))) # n) in Hvx as (?&?&Hfilter'); eauto.
          eapply sem_var_det in Hv; eauto. rewrite <-Hv.
          edestruct Hwc as (Hca'&Hck'); eauto. eapply Hsc' in Hv'; eauto.
          eapply sem_clock_equiv in Hsemck. specialize (Hsemck n). rewrite 2 tr_Stream_nth, ac_nth in Hsemck.
          eapply sem_clock_equiv in Hv'. specialize (Hv' n).
          unfold fselectb, fselect in Hv'. rewrite 2 tr_Stream_nth, ac_nth, mask_nth, Nat.eqb_refl, ffilter_nth in Hv'.
          setoid_rewrite Str_nth_map in Hv'. setoid_rewrite Hscn in Hv'. rewrite equiv_decb_refl in Hv'. inv Hv'.
          inv Hfilter'. apply eqst_ntheq with (n:=n) in H2. rewrite mask_nth, Nat.eqb_refl in H2.
          eapply filter_nth with (n:=n) in H1 as [(Hscn'&Hx&Hy)|[(Hscn'&Hx)|(?&Hscn'&?&?)]].
          1,3:setoid_rewrite Str_nth_map in Hscn'; setoid_rewrite Hscn in Hscn'; congruence.
          rewrite Hx. rewrite Hscn in Hsemck. apply IStr.sem_clock_instant_true_inv in Hsemck.
          rewrite H2 in H0. destruct (ys # n); try congruence.
      - exfalso. eapply Hnin; eauto.
    Qed.

    Lemma sc_var_inv_local :
      forall Γ (locs : list (ident * (type * clock * ident * option (exp * ident)))) Hi Hl Hi' Hl' bs cx,
        (forall x, InMembers x locs -> ~In x (map fst Γ)) ->
        Forall (fun x => wc_clock (idck (Γ ++ senv_of_locs locs)) (snd x)) (map (fun '(x, (_, ck, _, _)) => (x, ck)) locs) ->
        (forall x, IsLast Γ x -> Env.In x Hl) ->
        (forall x vs, sem_var Hi' x vs -> ~ InMembers x locs -> sem_var Hi x vs) ->
        Env.refines (EqSt (A:=svalue)) Hl Hl' ->
        Env.refines (EqSt (A:=svalue)) Hi (Env.union Hi (Env.restrict Hi' (map fst Γ ++ map fst locs))) ->
        (forall x, HasCaus Γ x cx \/ HasLastCaus Γ x cx -> sc_var_inv Γ (Hi, Hl) bs cx) ->
        (forall x, HasCaus (senv_of_locs locs) x cx \/ HasLastCaus (senv_of_locs locs) x cx ->
         sc_var_inv (senv_of_locs locs) (Env.union Hi Hi', Hl') bs cx) ->
        sc_var_inv
          (Γ ++ senv_of_locs locs)
          (Env.union Hi (Env.restrict Hi' (map fst Γ ++ map fst locs)), Hl') bs cx.
    Proof.
      intros * Hnd Hwc Hdom2 Href1 Href2 Href3 Hsc1 Hsc2.
      split; intros ??? Hca Hck Hv;
        rewrite HasClock_app in Hck; (rewrite HasCaus_app in Hca||rewrite HasLastCaus_app in Hca);
        destruct Hck as [Hck|Hck].
      - destruct Hca as [Hca|Hca].
        2:{ exfalso. inv Hca. inv Hck. simpl_In.
            eapply Hnd; eauto using In_InMembers. solve_In. }
        eapply sem_clock_refines; [eapply Href3|].
        edestruct Hsc1 as (Hinv&_); eauto.
        eapply Hinv; eauto. apply sem_var_union in Hv as [Hv|Hv]; auto.
        apply sem_var_restrict_inv in Hv as (Hin&Hv). apply in_app_iff in Hin as [Hin|Hin].
        + eapply Href1; eauto. intro contra. eapply Hnd; eauto using In_InMembers.
        + exfalso. eapply Hnd. apply fst_InMembers; eauto.
          inv Hca. solve_In.
      - destruct Hca as [Hca|Hca].
        1:{ exfalso. inv Hca. inv Hck. simpl_In.
            eapply Hnd; eauto using In_InMembers. solve_In. }
        edestruct Hsc2 as (Hinv&_); eauto.
        eapply sem_clock_refines', Hinv; eauto.
        + inv Hck; simpl_In. eapply Forall_forall, wc_clock_wx_clock in Hwc; eauto.
          2:solve_In. eauto.
        + intros ?? Hin' Hv'. inv Hv'.
          { eapply Env.union_find4' in H0 as [(Hfind1&Hfind2)|Hfind2].
            - econstructor; eauto.
              eapply Env.union_find2; eauto using Env.restrict_find_None.
            - econstructor; eauto.
              eapply Env.union_find3', Env.restrict_find; eauto.
              inv Hin'. erewrite fst_InMembers, map_app, map_fst_senv_of_locs in H; auto.
          }
        + eapply sem_var_refines; [|eauto]. intros ?? Hfind.
          { eapply Env.union_find4' in Hfind as [(Hfind1&Hfind2)|Hfind2].
            - destruct (Env.find x0 Hi') eqn:Hfind3.
              + assert (v ≡ s).
                { eapply sem_var_det with (H:=Hi). econstructor; eauto; reflexivity.
                  eapply Href1; eauto. econstructor; eauto; reflexivity.
                   intro contra. eapply Env.restrict_find in Hfind3. rewrite Hfind3 in Hfind2; congruence.
                  rewrite in_app_iff, <-2 fst_InMembers; auto. }
               do 2 esplit; eauto. eapply Env.union_find3'; eauto.
              + do 2 esplit; try reflexivity.
                eapply Env.union_find2; eauto.
            - eapply Env.restrict_find_inv in Hfind2 as (?&?).
              do 2 esplit; try reflexivity.
              eapply Env.union_find3'; eauto. }
      - destruct Hca as [Hca|Hca].
        2:{ exfalso. inv Hca. inv Hck. simpl_In.
            eapply Hnd; eauto using In_InMembers. solve_In. }
        eapply sem_clock_refines; [eapply Href3|].
        edestruct Hsc1 as (_&Hinv); eauto.
        eapply Hinv; eauto. solve_In.
        eapply sem_var_refines'; [|eauto|eauto].
        eapply Hdom2. inv Hca. econstructor; eauto. congruence.
      - destruct Hca as [Hca|Hca].
        1:{ exfalso. inv Hca. inv Hck. simpl_In.
            eapply Hnd; eauto using In_InMembers. solve_In. }
        edestruct Hsc2 as (_&Hinv); eauto.
        eapply sem_clock_refines', Hinv; eauto.
        + inv Hck; simpl_In. take (Forall (fun _ => wc_clock _ _) _) and eapply Forall_forall in it; eauto.
          2:solve_In. simpl in *. eapply wc_clock_wx_clock in it; eauto.
        + intros ?? Hin' Hv'. inv Hv'.
          { eapply Env.union_find4' in H0 as [(Hfind1&Hfind2)|Hfind2].
            - econstructor; eauto.
              eapply Env.union_find2; eauto using Env.restrict_find_None.
            - econstructor; eauto.
              eapply Env.union_find3', Env.restrict_find; eauto.
              inv Hin'. rewrite fst_InMembers, map_app, map_fst_senv_of_locs in H; auto.
          }
    Qed.

    Fact choose_first_ac {A} : forall bs xs ys,
        slower xs bs ->
        abstract_clock ys ≡ bs ->
        @abstract_clock A (choose_first xs ys) ≡ bs.
    Proof.
      intros * Hslow Hac.
      apply ntheq_eqst; intros n. apply eqst_ntheq with (n:=n) in Hac.
      rewrite ac_nth in Hac.
      rewrite ac_nth, choose_first_nth.
      destruct (xs # n) eqn:Hx; auto.
      destruct (bs # n) eqn:Hb; auto.
      eapply slower_nth in Hslow; eauto. congruence.
    Qed.

    Fact const_stres_ac {A} : forall bs (x : A),
        abstract_clock (const_stres bs x) ≡ bs.
    Proof.
      intros *.
      apply ntheq_eqst; intros n. rewrite ac_nth. setoid_rewrite Str_nth_map.
      destruct (bs # n); auto.
    Qed.

    Lemma sc_transitions' Γty Γ : forall Hi bs' trans def stres,
        wc_global G ->
        NoDupMembers Γ ->
        Forall (fun '(e, _) => wt_exp G Γty e) trans ->
        Forall (fun '(e, _) => wc_exp G Γ e /\ clockof e = [Cbase]) trans ->
        (forall cx, Exists (fun '(e, _) => Is_free_left Γ cx 0 e) trans -> sc_var_inv Γ Hi bs' cx) ->
        sem_transitions G Hi bs' trans def stres ->
        abstract_clock stres ≡ bs'.
    Proof.
      induction trans; intros * HwG Hnd Hwt Hwc Hsc Hsem;
        inv Hwt; inv Hwc; inv Hsem; destruct_conjs.
      - rewrite H0, const_stres_ac. reflexivity.
      - rewrite H13. apply choose_first_ac; eauto.
        eapply sc_exp' with (k:=0) in H6; eauto.
        2:{ rewrite <-length_clockof_numstreams. take (clockof _ = _) and rewrite it; auto. }
        take (clockof _ = _) and rewrite it in H6. simpl in *.
        eapply sc_slower in H6; eauto using ac_aligned.
        apply slower_nth; intros * Hbs. setoid_rewrite Str_nth_map.
        apply slower_nth with (n:=n) in H6; auto.
        apply bools_of_nth with (n:=n) in H7 as [(Hv&Hx)|[(Hv&Hx)|(?&Hx)]].
        + setoid_rewrite H6 in Hv; congruence.
        + setoid_rewrite H6 in Hv; congruence.
        + rewrite Hx; auto.
    Qed.

    Lemma sc_var_inv_subclock Γ Γ' : forall Hi bs bs' cx ck,
        sem_clock (fst Hi) bs ck bs' ->
        (forall x ck', HasClock Γ' x ck' -> HasClock Γ x ck /\ ck' = Cbase) ->
        (forall x, HasCaus Γ' x cx -> HasCaus Γ x cx) ->
        (forall x, HasLastCaus Γ' x cx -> HasLastCaus Γ x cx) ->
        sc_var_inv Γ Hi bs cx ->
        sc_var_inv Γ' Hi bs' cx.
    Proof.
      intros * Hsemck Hck Hca Hlca (Hinv1&Hinv2).
      split; intros * Hasca Hasck Hv.
      - edestruct Hck as (Hasck'&?); eauto; subst.
        eapply Hinv1 in Hv; eauto.
        eapply sem_clock_det in Hsemck; eauto. constructor; symmetry; auto.
      - edestruct Hck as (Hasck'&?); eauto; subst.
        eapply Hinv2 in Hv; eauto.
        eapply sem_clock_det in Hsemck; eauto. constructor; symmetry; auto.
    Qed.

    Lemma sc_scope {A} f_idcaus P_nd P_vd P_wt P_wc (P_blk1 P_blk2 : _ -> _ -> Prop) P_dep :
      forall envS locs (blks: A) Γ Γty xs Hi bs cy,
        wc_global G ->
        NoDup (map snd (idcaus_of_senv Γ ++ idcaus_of_scope f_idcaus (Scope locs blks))) ->
        NoDupMembers Γ ->
        NoDupScope P_nd (map fst Γ) (Scope locs blks) ->
        VarsDefinedScope P_vd (Scope locs blks) xs ->
        incl xs (map fst Γ) ->
        wt_scope P_wt G Γty (Scope locs blks) ->
        wc_env (idck Γ) ->
        wc_scope P_wc G Γ (Scope locs blks) ->
        sem_scope_ck' P_blk1 envS Hi bs (Scope locs blks) ->
        Env.dom_ub (fst Hi) (map fst Γ) ->
        (forall x, IsLast Γ x -> Env.In x (snd Hi)) ->
        (forall x cx, HasCaus Γ x cx \/ HasLastCaus Γ x cx ->
                 depends_on_scope P_dep Γ cy cx (Scope locs blks) -> sc_var_inv Γ Hi bs cx) ->
        (forall cx, In cx (map snd (idcaus_of_scope f_idcaus (Scope locs blks))) ->
               depends_on_scope P_dep Γ cy cx (Scope locs blks) -> In cx envS) ->
        (forall Γ xs Hi Hi' Hl,
            P_vd blks xs ->
            P_nd Γ blks ->
            incl xs Γ ->
            Env.refines (@EqSt _) Hi Hi' -> P_blk1 (Hi, Hl) blks -> P_blk1 (Hi', Hl) blks) ->
        (forall Γ xs Hi Hl,
            P_vd blks xs ->
            P_nd (map fst Γ) blks ->
            incl xs (map fst Γ) ->
            P_wc Γ blks ->
            P_blk1 (Hi, Hl) blks -> P_blk1 (Env.restrict Hi (map fst Γ), Hl) blks) ->
        (forall Γ Γty xs Hi,
            NoDup (map snd (idcaus_of_senv Γ ++ f_idcaus blks)) ->
            NoDupMembers Γ ->
            P_nd (map fst Γ) blks ->
            P_vd blks xs ->
            incl xs (map fst Γ) ->
            P_wt Γty blks ->
            wc_env (idck Γ) ->
            P_wc Γ blks ->
            P_blk1 Hi blks ->
            Env.dom_ub (fst Hi) (map fst Γ) ->
            (forall x, IsLast Γ x -> Env.In x (snd Hi)) ->
            (forall x cx, HasCaus Γ x cx \/ HasLastCaus Γ x cx ->
                     P_dep Γ cy cx blks -> sc_var_inv Γ Hi bs cx) ->
            (forall cx, In cx (map snd (f_idcaus blks)) ->
                   P_dep Γ cy cx blks -> In cx envS) ->
            (forall y, In y xs -> HasCaus Γ y cy -> sc_var_inv Γ Hi bs cy)
            /\ P_blk2 Hi blks) ->
        (forall y, In y xs -> HasCaus Γ y cy -> sc_var_inv Γ Hi bs cy)
        /\ sem_scope_ck' P_blk2 (cy::envS) Hi bs (Scope locs blks).
    Proof.
      intros * HwcG Hnd1 Hnd2 Hnd4 Hvars Hincl Hwt Henv Hwc Hsem Hdom Hdoml Hsc HenvP Href Hres Hind;
        inv Hnd4; inv Hvars; inv Hwt; inv Hwc; inv Hsem; simpl in *.

      assert (Env.refines (EqSt (A:=svalue)) Hi0
                          (Env.union Hi0 (Env.restrict Hi' (map fst Γ ++ map fst locs)))) as Href2.
      { intros ?? Hfind. destruct (Env.find x (Env.restrict Hi' (map fst Γ ++ map fst locs))) eqn:Hfind'.
        - exists s. split; eauto using Env.union_find3'.
          eapply sem_var_det; [now econstructor; try eapply Hfind|].
          eapply H2; eauto.
          + eapply sem_var_restrict_inv. now econstructor; eauto.
          + intros contra. eapply H4; eauto.
            eapply Env.dom_ub_use; eauto. econstructor; eauto.
        - exists v. split; try reflexivity.
          eapply Env.union_find2; eauto. }

      assert (forall x cx,
                 HasCaus (Γ ++ senv_of_locs locs) x cx \/ HasLastCaus (Γ ++ senv_of_locs locs) x cx ->
                 depends_on_scope P_dep Γ cy cx (Scope locs blks) ->
                 sc_var_inv (Γ ++ senv_of_locs locs) (Env.union Hi0 (Env.restrict Hi' (map fst Γ ++ map fst locs)), Hl') bs cx
             ) as Hscloc.
      { intros * _ Hdep. eapply sc_var_inv_local; eauto.
        - simpl_Forall; auto.
        - intros * Hca. apply idcaus_of_senv_In in Hca.
          eapply Forall_forall in H18; eauto. eapply HenvP; eauto.
          rewrite map_app, in_app_iff. left. solve_In. }

      edestruct Hind with (Hi:=(Env.union Hi0 (Env.restrict Hi' (map fst Γ ++ map fst locs)), Hl'))
                          (Γ:=Γ ++ senv_of_locs locs) as (Hsc'&Hcons); eauto using in_or_app.
      1:{ now rewrite idcaus_of_senv_app, <-app_assoc. }
      1:{ apply NoDupMembers_app; auto.
          - now apply NoDupMembers_senv_of_locs.
          - intros. rewrite InMembers_senv_of_locs. intros ?.
            eapply H4, fst_InMembers; eauto. }
      1:{ now rewrite map_app, map_fst_senv_of_locs. }
      1:{ rewrite map_app, map_fst_senv_of_locs.
          apply incl_appl'; auto. }
      1:{ simpl_app. apply wc_env_app; auto.
          simpl_Forall; auto. }
      1:{ eapply Href, Hres; eauto. 2-4:rewrite map_app, map_fst_senv_of_locs; auto.
          1,3:apply incl_appl'; auto.
          apply Env.union_refines4'; eauto using EqStrel. }
      1:{ simpl. rewrite map_app, map_fst_senv_of_locs.
          apply Env.union_dom_ub; auto using Env.restrict_dom_ub.
          eapply Env.dom_ub_incl; [|eauto]. solve_incl_app.
      }
      1:{ intros * Hin. inv Hin.
          apply in_app_iff in H as [|]; simpl_In; subst.
          + eapply Env.In_refines; eauto with senv.
          + destruct o as [(?&?)|]; simpl in *; try congruence.
            edestruct H14 as (?&?&?&?&?&?&?); eauto using sem_var_In. }
      1:{ intros. eapply Hscloc; eauto. econstructor; eauto. }
      1:{ intros. eapply HenvP. 2:econstructor; eauto.
          rewrite map_app, in_app_iff; auto. }
      split.
      - intros * Hinxs Hca.
        split; intros ??? Hca' Hck Hv; simpl_In.
        + eapply HasCaus_snd_det in Hca; eauto; subst. 2:solve_NoDup_app.
          edestruct Hsc' as (Hsc1&_); eauto using in_or_app.
          apply HasCaus_app; auto.
          eapply sem_var_refines, Hsc1 in Hv; eauto using in_or_app.
          2:rewrite HasCaus_app; auto. 2:rewrite HasClock_app; eauto.
          eapply sem_clock_refines_iff; eauto.
          intros * Hfree.
          eapply wc_clock_is_free_in in Hfree; [|eauto].
          2:{ eapply wc_env_var; eauto. inv Hck; solve_In. }
          apply InMembers_In in Hfree as (?&?); solve_In.
          intros Henvin. apply Env.union_In in Henvin as [|Henvin]; auto.
          apply Env.restrict_In_iff in Henvin as (Henvin&_).
          inv Henvin. assert (sem_var Hi' x x1) as Hsemv by (econstructor; eauto; reflexivity).
          apply H2 in Hsemv. inv Hsemv; econstructor; eauto.
          intro contra. eapply H4; eauto; solve_In.
        + exfalso. eapply NoDup_HasCaus_HasLastCaus; eauto. solve_NoDup_app.

      - econstructor. 4:eauto. all:eauto.
        + intros * Hv Hnin.
          apply sem_var_union in Hv as [|Hvar]; auto.
          apply sem_var_restrict_inv in Hvar as (?&?); eauto.
        + intros. edestruct H14; eauto; destruct_conjs.
          do 3 esplit. repeat split; eauto.
          * simpl_Forall.
            eapply Sem.sem_exp_refines, Sem.sem_exp_restrict; eauto with lclocking.
            rewrite map_app, map_fst_senv_of_locs. apply Env.union_refines4'; auto using EqStrel.
          * eapply sem_var_refines, sem_var_restrict; eauto. apply Env.union_refines4'; auto using EqStrel.
            apply in_app_iff, or_intror; solve_In.
        + constructor.
          2:{ simpl_Forall. take (sc_var_inv _ _ _ _) and destruct it as (Hsc1&Hsc2).
              assert (forall x vs,
                         IsVar (Γ ++ senv_of_locs locs) x ->
                         sem_var (Env.union Hi0 Hi') x vs ->
                         sem_var (Env.union Hi0 (Env.union Hi0 (Env.restrict Hi' (map fst Γ ++ map fst locs)))) x vs) as Hvs.
              { intros ?? Hin' Hv'. inv Hv'.
                eapply Env.union_find4' in H15 as [(Hfind1&Hfind2)|Hfind2].
                - econstructor; eauto.
                  eapply Env.union_find3', Env.union_find2; eauto using Env.restrict_find_None.
                - econstructor; eauto.
                  eapply Env.union_find3', Env.union_find3', Env.restrict_find; eauto.
                  inv Hin'. rewrite fst_InMembers, map_app, map_fst_senv_of_locs in H0; auto.
              }

              split; intros * Hca Hck Hv; simpl in *; inv Hck; inv Hca; simpl_In; eapply NoDupMembers_det in Hin0; eauto; inv_equalities.
              1,2:eapply Forall_forall in H8 as Hck; [|solve_In; eauto]; simpl in *.
              1,2:eapply sem_clock_refines'; eauto with lclocking.
              - eapply Hsc1; eauto. 1,2:econstructor; solve_In; auto.
                inv Hv. take (Env.MapsTo _ _ _) and rename it into Hfind2.
                repeat eapply Env.union_find4' in Hfind2 as [(Hfind1&Hfind2)|Hfind2]; econstructor; eauto.
                + eapply Env.union_find2; eauto.
                  apply Env.union_find_None in Hfind2 as (_&Hfind2).
                  destruct (Env.find x0 Hi') eqn:Hfind; auto. eapply Env.restrict_find in Hfind. rewrite Hfind in Hfind2. congruence.
                  apply in_or_app, or_intror. solve_In.
                + eapply Env.union_find2; eauto.
                  destruct (Env.find x0 Hi') eqn:Hfind; auto. eapply Env.restrict_find in Hfind. rewrite Hfind in Hfind2. congruence.
                  apply in_or_app, or_intror. solve_In.
                + apply Env.restrict_find_inv in Hfind2 as (?&?). apply Env.union_find3'; auto.
              - eapply Hsc2; eauto. 1,2:econstructor; solve_In; auto.
          }
          split; intros * Hca Hck Hv.
          * (* locs *)
            edestruct Hsc' as (Hsc1&_). 2:apply HasCaus_app; eauto.
            1:apply in_or_app, or_intror; inv Hca; solve_In.
            eapply sem_clock_refines, Hsc1; eauto. 2:apply HasCaus_app; eauto. 2:apply HasClock_app; eauto.
            apply Env.union_refines4'; auto using EqStrel.
            apply sem_var_union in Hv as [Hv|]; auto. simpl in *.
            eapply sem_var_refines; eauto.

          * (* lasts *)
            inv Hca. inv Hck. simpl_In. eapply NoDupMembers_det in Hin0; eauto; inv Hin0.
            simpl_Forall.
            edestruct H14 as (?&?&?&He&Hv1&Hfby&Hv2); eauto.
            eapply sem_var_det in Hv; eauto. rewrite <-Hv.
            { eapply Sem.sem_exp_restrict, Sem.sem_exp_refines, sc_exp' with (Γ:=Γ++senv_of_locs locs) (k:=0) in He; eauto with lclocking; simpl in *.
              - take (clockof e = _) and setoid_rewrite it in He; simpl in He.
                apply ac_fby1 in Hfby. rewrite <-Hfby.
                eapply sem_clock_refines; eauto.
                eapply Env.union_refines4', EqStrel.
              - apply NoDupMembers_app; auto.
                + apply NoDupMembers_senv_of_locs; auto.
                + intros. rewrite InMembers_senv_of_locs. intros ?.
                  eapply H4, fst_InMembers; eauto.
              - rewrite <-length_clockof_numstreams, H0; auto.
              - intros ? Hfree. edestruct Is_free_left_In_snd; eauto.
                eapply Hscloc; eauto.
                eapply DepOnScope2; eauto. solve_Exists.
              - rewrite map_app, map_fst_senv_of_locs; auto.
                apply Env.union_refines4'; auto using EqStrel.
            }
    Qed.

    Lemma sc_block : forall envP blk xs Γ Γty Hi bs cy,
        wc_global G ->
        NoDup (map snd (idcaus_of_senv Γ ++ idcaus_of_locals blk)) ->
        NoDupMembers Γ ->
        NoDupLocals (map fst Γ) blk ->
        VarsDefined blk xs ->
        incl xs (map fst Γ) ->
        wt_block G Γty blk ->
        wc_env (idck Γ) ->
        wc_block G Γ blk ->
        sem_block_ck' envP Hi bs blk ->
        Env.dom_ub (fst Hi) (map fst Γ) ->
        (forall x, IsLast Γ x -> Env.In x (snd Hi)) ->
        (forall x cx, HasCaus Γ x cx \/ HasLastCaus Γ x cx -> depends_on Γ cy cx blk -> sc_var_inv Γ Hi bs cx) ->
        (forall cx, In cx (map snd (idcaus_of_locals blk)) -> depends_on Γ cy cx blk -> In cx envP) ->
        (forall y, In y xs -> HasCaus Γ y cy -> sc_var_inv Γ Hi bs cy)
        /\ sem_block_ck' (cy::envP) Hi bs blk.
    Proof.
      induction blk as [(xs&es)| | | |] using block_ind2;
        intros * HwG Hnd1 Hnd2 Hnd4 Hvars Hincl Hwt Henv Hwc Hsem Hdom Hdoml Hsc HenvP;
        inv Hnd4; inv Hvars; inv Hwt; inv Hwc; inv Hsem; simpl in *.

      - (* equation *)
        split; [|constructor; auto].
        intros * Hinxs Hca.
        eapply In_nth with (d:=xH) in Hinxs as (?&Hlen&Hnth); subst.
        eapply sc_exp_equation in H4; rewrite app_nil_r in *; eauto.
        intros * Hfree.
        assert (Hfree':=Hfree). eapply Is_free_left_list_In_snd in Hfree as (?&?); eauto.
        eapply Hsc; eauto.
        econstructor; eauto.
        eapply nth_error_nth'; eauto.

      - (* reset *)
        assert (forall k, Forall (fun blks => (forall y xs, VarsDefined blks xs -> In y xs -> HasCaus Γ y cy ->
                                               sc_var_inv Γ (Sem.mask_hist k r Hi) (maskb k r bs) cy)
                                      /\ sem_block_ck' (cy::envP) (Sem.mask_hist k r Hi) (maskb k r bs) blks) blocks) as Hf.
        { intros *. specialize (H14 k). simpl_Forall. inv_VarsDefined.
          edestruct H with (xs:=xs). 10:eauto. all:eauto.
          - clear - H0 Hnd1. eapply NoDup_locals_inv; eauto.
          - etransitivity; eauto using incl_concat.
          - unfold Sem.mask_hist. eapply Env.dom_ub_map in Hdom; eauto.
          - setoid_rewrite Env.Props.P.F.map_in_iff; eauto.
          - intros * Hin' Hdep. eapply sc_var_inv_mask; eauto.
            eapply Hsc; eauto. constructor; solve_Exists.
          - intros * Hin' Hdep. eapply HenvP; eauto. solve_In.
            constructor; solve_Exists.
          - split; eauto.
            intros * HDef' Hin' Hca. eapply H1; eauto.
            eapply VarsDefined_det in Hdef; eauto. now rewrite <-Hdef.
        }
        split.
        + intros * Hinxs Hca.
          apply in_concat in Hinxs as (?&Hin1&Hin2). inv_VarsDefined. simpl_Forall.
          eapply sc_var_inv_unmask; intros.
          specialize (Hf k). simpl_Forall; eauto.
        + econstructor; eauto.
          intros k. specialize (Hf k). simpl_Forall; eauto.

      - (* switch *)
        assert (Is_defined_in Γ cy (Bswitch ec branches) \/ Is_last_in cy (Bswitch ec branches) ->
                sem_clock (fst Hi) bs ck (abstract_clock sc)) as Hsemck.
        { intros.
          assert (Hsem:=H15). eapply sc_exp' with (Γ:=Γ) (k:=0) in Hsem; eauto.
          2:{ rewrite <-length_clockof_numstreams, H12; auto. }
          2:{ intros ? Hfree. assert (Hfree':=Hfree). apply Is_free_left_In_snd in Hfree' as (?&?).
              eapply Hsc; eauto.
              eapply DepOnSwitch2; eauto.
          }
          take (clockof _ = [_]) and rewrite it in Hsem; simpl in *; auto.
        }

        assert (Forall (fun '(k, s) => exists Hi',
                            Sem.filter_hist k sc Hi Hi'
                            /\ (forall y, In y xs -> HasCaus (map (fun '(x, e) => (x, ann_with_clock e Cbase)) Γ) y cy -> sc_var_inv (map (fun '(x, e) => (x, ann_with_clock e Cbase)) Γ) Hi' (ffilterb k sc bs) cy) /\
                              sem_scope_ck'
                                (fun Hi => Forall (sem_block_ck' (cy::envP) Hi (ffilterb k sc bs)))
                                (cy :: envP) Hi' (ffilterb k sc bs) s)
                       branches) as Hf.
        { simpl_Forall. do 2 esplit; eauto.
          destruct s. eapply sc_scope
                        with (P_dep:=fun Γ cx cy => Exists (depends_on Γ cx cy))
                             (Γ:=map (fun '(x, e) => (x, ann_with_clock e Cbase)) Γ) in H18 as (Hsc'&?); eauto.
          - clear - H0 Hnd1.
            eapply NoDup_locals_inv2; eauto.
            unfold idcaus_of_senv in *. erewrite map_map, map_filter_map, map_ext with (l:=Γ), map_filter_ext with (xs:=Γ); eauto.
            1,2:intros; destruct_conjs; auto.
          - apply nodupmembers_map; auto.
          - erewrite map_map, map_ext; eauto. intros; destruct_conjs; auto.
          - erewrite map_map, map_ext; eauto. intros; destruct_conjs; auto.
          - apply Forall_forall; intros ? Hin. simpl_In. constructor.
          - eapply wc_scope_incl; [| |eauto|].
            + intros * Has. eapply H14 in Has as (Has&?).
              inv Has. econstructor; solve_In. auto.
            + intros * His. eapply H16 in His.
              inv His. econstructor; solve_In. auto.
            + intros; simpl in *; simpl_Forall; eauto using wc_block_incl.
          - destruct H1 as (Href&_). eapply Env.dom_ub_refines; eauto.
            erewrite map_map, map_ext; eauto. intros; destruct_conjs; auto.
          - intros ? His. destruct H1 as (_&Heq). rewrite Heq. setoid_rewrite Env.Props.P.F.map_in_iff.
            eapply Hdoml. inv His; simpl_In. econstructor; eauto.
          - intros * ? Hdep.
            assert (forall x, HasCaus Γ x cx \/ HasLastCaus Γ x cx -> In x (map fst Γ')) as Hgamma.
            { intros * Has. eapply depends_scope_In with (x:=x0) in Hdep; eauto with lclocking.
              - inv Hdep. rewrite <-fst_InMembers; eauto.
              - clear - H0 Hnd1.
                eapply NoDup_locals_inv2; eauto. auto.
                unfold idcaus_of_senv in *. simpl_app.
                erewrite map_map with (l:=Γ), map_ext with (l:=Γ), map_filter_map, map_filter_ext; eauto.
                1,2:intros; destruct_conjs; auto.
              - destruct Has as [Has|Has]; inv Has; [left|right]; econstructor; solve_In; auto.
              - erewrite map_map, map_ext; eauto. intros; destruct_conjs; auto.
              - eapply wc_scope_wx_scope; eauto.
              - intros; simpl in *. simpl_Exists; simpl_Forall.
                eapply depends_on_In; eauto using NoDup_locals_inv with lclocking.
            }
            assert (forall x ck', HasCaus Γ x cx \/ HasLastCaus Γ x cx -> HasClock Γ x ck' -> ck' = ck) as Hgamma2.
            { intros * Hing Hck. apply Hgamma in Hing. simpl_In.
              edestruct H14 as (Hck'&?); eauto. econstructor; solve_In; eauto.
              inv Hck. inv Hck'. eapply NoDupMembers_det in H22; eauto. congruence. }
            split; intros ??? Hca Hck Hv; inv Hca; inv Hck; simpl_In.
            1,2:eapply NoDupMembers_det in Hin0; eauto; subst.
            1,2:assert (a0.(clo) = ck) by (eapply Hgamma2; eauto with senv); subst.
            + destruct H1 as (Hfilter&_). eapply sem_var_filter_inv in Hv as (?&Hv&Heq); eauto.
              apply filter_ffilter in Heq. rewrite Heq, ac_ffilter.
              assert (depends_on Γ cy (causl a0) (Bswitch ec branches)) as Hdep2.
              { eapply depends_on_incl. 3:econstructor; solve_Exists.
                1,2:intros * Has; inv Has; simpl_In; eauto with senv. }
              eapply Hsc in Hv. 4,5:eauto with senv. 2,3:eauto with senv.
              eapply sem_clock_det in Hv. 2:eapply Hsemck; eauto using depends_on_def_last. rewrite <-Hv.
              eapply sem_clock_filter; eauto using depends_on_def_last.
            + destruct H1 as (?&Hfilter). rewrite Hfilter in Hv.
              eapply sem_var_ffilter_inv in Hv as (?&Hv&Heq). rewrite Heq, ac_ffilter.
              assert (depends_on Γ cy cx (Bswitch ec branches)) as Hdep2.
              { eapply depends_on_incl. 3:econstructor; solve_Exists.
                1,2:intros * Has; inv Has; simpl_In; eauto with senv. }
              eapply Hsc in Hv. 4,5:eauto with senv. 2,3:eauto with senv.
              eapply sem_clock_det in Hv. 2:eapply Hsemck; eauto using depends_on_def_last. rewrite <-Hv.
              eapply sem_clock_filter; eauto using depends_on_def_last.
          - intros ? Hin' Hdep. apply HenvP. solve_In.
            eapply depends_on_incl. 3:econstructor; solve_Exists.
            1,2:intros * Has; inv Has; simpl_In; eauto with senv.
          - intros; simpl in *; simpl_Forall; inv_VarsDefined.
            eapply sem_block_ck'_refines; eauto.
            eapply NoDupLocals_incl; [|eauto]. etransitivity; eauto. rewrite <-H26; eauto using incl_concat.
          - intros; simpl in *; simpl_Forall; inv_VarsDefined.
            eapply sem_block_ck'_restrict; eauto.
            eapply NoDupLocals_incl; [|eauto]. etransitivity; eauto. rewrite <-H26; eauto using incl_concat.
          - intros; simpl in *; simpl_Forall.
            assert (Forall (fun blks => (forall y xs, VarsDefined blks xs -> In y xs -> HasCaus Γ0 y cy ->
                                              sc_var_inv Γ0 Hi0 (ffilterb e sc bs) cy)
                                     /\ sem_block_ck' (cy::envP) Hi0 (ffilterb e sc bs) blks) l0) as Hf.
            { simpl_Forall. inv_VarsDefined.
              edestruct H with (Γ:=Γ0) (xs:=xs1). 10:eauto. all:eauto.
              - eapply NoDup_locals_inv; eauto.
              - etransitivity; eauto using incl_concat.
                take (Permutation _ _) and now rewrite it.
              - intros * Hin' Hdep. eapply H31; eauto. solve_Exists.
              - intros * Hin' Hdep. eapply H32; eauto.
                2:solve_Exists. solve_In.
              - split; eauto.
                intros * Hdef' Hin' Hca. eapply H23; eauto.
                eapply VarsDefined_det in Hdef; eauto. now rewrite <-Hdef.
            } clear H.
            split.
            + intros * Hinxs Hca. inv_VarsDefined.
              rewrite <-Hperm in Hinxs. apply in_concat in Hinxs as (?&?&?); inv_VarsDefined; simpl_Forall.
              eapply H33; eauto.
            + simpl_Forall; eauto.
        } clear H H21.
        split.
        + intros * Hinxs Hca1.
          assert (Syn.Is_defined_in y (Bswitch ec branches)) as Hdef.
          { eapply VarsDefined_Is_defined; eauto. econstructor; eauto.
            eapply NoDupLocals_incl; [|econstructor; eauto]. auto. }
          assert (Is_defined_in Γ cy (Bswitch ec branches)) as Hdef' by (eauto using Is_defined_in_Is_defined_in).
          eapply sc_var_inv_unfilter with (tn:=tn) (Γ':=map (fun '(x, e) => (x, ann_with_clock e Cbase)) Γ); eauto.
          * destruct tn as (?&[]); simpl in *; try lia.
            apply Permutation_sym, Permutation_nil, map_eq_nil in H8; congruence.
          * rewrite H6 in H20; inv H20; eauto.
          * intros * Hca Hck.
            eapply HasCaus_snd_det in Hca1; eauto; [|simpl_app; eauto using NoDup_app_l]; subst.
            inv Hck. inv Hca.
            split; econstructor; solve_In; auto.
          * intros * Hca Hck.
            eapply HasCaus_snd_det in Hca1; eauto; [|simpl_app; eauto using NoDup_app_l]; subst.
            inv Hck. inv Hca. eapply NoDupMembers_det in H0; eauto. subst.
            assert (clo e = ck) as Heq; try (rewrite Heq; eauto).
            inv Hdef. rename H18 into Hdef. simpl_Exists; simpl_Forall.
            destruct s. eapply wc_scope_Is_defined_in in Hdef; eauto.
            2:{ intros; simpl_Exists; simpl_Forall; eauto using wc_block_Is_defined_in. }
            eapply InMembers_In in Hdef as (?&Hin').
            edestruct H14 as (Hck&_); eauto with senv.
            inv Hck. eapply NoDupMembers_det in H; eauto. congruence.
          * intros * Hin. rewrite <-H8 in Hin. simpl_In; simpl_Forall.
            do 2 esplit; [|split; eauto].
            1:{ intros ? Hca.
                eapply HasCaus_snd_det in Hca1; eauto; [|simpl_app; eauto using NoDup_app_l]; subst.
                destruct s. eapply sem_scope_defined1; eauto.
                inv H1; econstructor; eauto; simpl_Forall; eauto using sem_block_ck'_sem_block.
            }
            eapply H0; eauto. inv Hca1; econstructor; solve_In. auto.
          * intros * Hnin. eapply NoDup_HasCaus_HasLastCaus; eauto. solve_NoDup_app.
        + econstructor; eauto. simpl_Forall; eauto.

      - (* automaton *)
        assert (Is_defined_in Γ cy (Bauto ck (ini0, oth) states) \/ Is_last_in cy (Bauto ck (ini0, oth) states) ->
                bs' ≡ abstract_clock stres) as Hac.
        { intros * Hdef.
          symmetry. eapply sc_transitions' with (Γ:=map_filter (fun '(x, e) => if e.(clo) ==b ck then Some (x, ann_with_clock e Cbase) else None) Γ) in H23; eauto. 3,4:simpl_Forall; eauto.
          - apply ac_fby1 in H24. now rewrite <-H24.
          - apply nodupmembers_map_filter; auto.
            intros; destruct (_ ==b _); simpl; auto.
          - split; auto.
            eapply wc_exp_incl; [| |eauto].
            + intros * Has. eapply H16 in Has as (Has&?).
              inv Has. econstructor. solve_In; simpl. rewrite equiv_decb_refl; eauto.
              auto.
            + intros * His. eapply H17 in His as His'.
              inv His; inv His'. edestruct H16 as (Has&?); eauto with senv.
              inv Has. eapply NoDupMembers_det in H21; eauto; subst.
              econstructor. solve_In; simpl. rewrite equiv_decb_refl; eauto.
              simpl; auto.
          - intros * Hex. simpl_Exists.
            assert (forall x cx, HasCaus (map_filter (fun '(x0, e1) => if clo e1 ==b ck then Some (x0, ann_with_clock e1 Cbase) else None) Γ) x cx -> HasCaus Γ x cx) as Hca.
            { intros * Hca; inv Hca; simpl_In.
              destruct (_ ==b _) eqn:Hck; inv Hf. rewrite equiv_decb_equiv in Hck; inv Hck.
              eauto with senv. }
            assert (forall x cx, HasLastCaus (map_filter (fun '(x0, e1) => if clo e1 ==b ck then Some (x0, ann_with_clock e1 Cbase) else None) Γ) x cx -> HasLastCaus Γ x cx) as Hlca.
            { intros * Hlca; inv Hlca; simpl_In.
              destruct (_ ==b _) eqn:Hck; inv Hf. rewrite equiv_decb_equiv in Hck; inv Hck.
              eauto with senv. }
            eapply sc_var_inv_subclock with (Γ:=Γ); eauto.
            + intros * Hck; inv Hck; simpl_In.
              destruct (_ ==b _) eqn:Hck; inv Hf. rewrite equiv_decb_equiv in Hck; inv Hck.
              eauto with senv.
            + eapply Is_free_left_In_snd in Hex as Hca'. destruct Hca' as (?&Hca').
              eapply Hsc; eauto. destruct Hca'; eauto.
              eapply DepOnAuto3; eauto.
              solve_Exists. eapply Is_free_left_incl in Hex; eauto.
        }
        assert (Forall (fun '(e, s) => forall k, exists Hi',
                            Sem.select_hist e k stres Hi Hi'
                            /\ (forall y, In y xs -> HasCaus (map (fun '(x, e) => (x, ann_with_clock e Cbase)) Γ) y cy ->
                                    sc_var_inv (map (fun '(x, e) => (x, ann_with_clock e Cbase)) Γ) Hi' (fselectb e k stres bs) cy) /\
                              sem_scope_ck'
                                (fun Hi blks => Forall (sem_block_ck' (cy::envP) Hi (fselectb e k stres bs)) (fst blks)
                                             /\ sem_transitions G Hi (fselectb e k stres bs) (snd blks) (e, false) (fselect absent e k stres stres1))
                                (cy :: envP) Hi' (fselectb e k stres bs) s)
                       states) as Hf.
        { simpl_Forall. intros. specialize (H25 k); destruct_conjs. destruct s as [?(?&?)].
          do 2 esplit; eauto.
          eapply sc_scope
            with (P_dep:=fun Γ cx cy blks => Exists (depends_on Γ cx cy) (fst blks))
                 (Γ:=map (fun '(x, e) => (x, ann_with_clock e Cbase)) Γ) in H3 as (Hsc'&?); eauto.
          - clear - H0 Hnd1.
            eapply NoDup_locals_inv2; eauto.
            unfold idcaus_of_senv in *. erewrite map_map, map_filter_map, map_ext with (l:=Γ), map_filter_ext with (xs:=Γ); eauto.
            1,2:intros; destruct_conjs; auto.
          - apply nodupmembers_map; auto.
          - erewrite map_map, map_ext; eauto. intros; destruct_conjs; auto.
          - erewrite map_map, map_ext; eauto. intros; destruct_conjs; auto.
          - apply Forall_forall; intros ? Hin. simpl_In. constructor.
          - eapply wc_scope_incl; [| |eauto|].
            + intros * Has. eapply H16 in Has as (Has&?).
              inv Has. econstructor; solve_In. auto.
            + intros * His. eapply H17 in His.
              inv His. econstructor; solve_In. auto.
            + intros; simpl in *.
              destruct_conjs; split; eauto; simpl_Forall; eauto using wc_block_incl, wc_exp_incl.
          - destruct H1 as (Href&_). eapply Env.dom_ub_refines; eauto.
            erewrite map_map, map_ext; eauto. intros; destruct_conjs; auto.
          - intros ? His. destruct H1 as (_&Heq). rewrite Heq. setoid_rewrite Env.Props.P.F.map_in_iff.
            eapply Hdoml. inv His; simpl_In. econstructor; eauto.
          - intros * ? Hdep.
            assert (forall x, HasCaus Γ x cx \/ HasLastCaus Γ x cx -> In x (map fst Γ')) as Hgamma.
            { intros * Has. eapply depends_scope_In with (x:=x0) in Hdep; eauto with lclocking.
              - inv Hdep. rewrite <-fst_InMembers; eauto.
              - clear - H0 Hnd1.
                eapply NoDup_locals_inv2; eauto. auto.
                unfold idcaus_of_senv in *. simpl_app.
                erewrite map_map with (l:=Γ), map_ext with (l:=Γ), map_filter_map, map_filter_ext; eauto.
                1,2:intros; destruct_conjs; auto.
              - destruct Has as [Has|Has]; inv Has; [left|right]; econstructor; solve_In; auto.
              - erewrite map_map, map_ext; eauto. intros; destruct_conjs; auto.
              - eapply wc_scope_wx_scope; eauto.
              - intros; simpl in *. simpl_Exists; simpl_Forall.
                eapply depends_on_In; eauto using NoDup_locals_inv with lclocking.
            }
            assert (forall x ck', HasCaus Γ x cx \/ HasLastCaus Γ x cx -> HasClock Γ x ck' -> ck' = ck) as Hgamma2.
            { intros * Hing Hck. apply Hgamma in Hing. simpl_In.
              edestruct H16 as (Hck'&?); eauto. econstructor; solve_In; eauto.
              inv Hck. inv Hck'. eapply NoDupMembers_det in H20; eauto. congruence. }
            split; intros ??? Hca Hck Hv; inv Hca; inv Hck; simpl_In.
            1,2:eapply NoDupMembers_det in Hin0; eauto; subst.
            1,2:assert (a0.(clo) = ck) by (eapply Hgamma2; eauto with senv); subst.
            + destruct H1 as (Hfilter&_). eapply sem_var_select_inv in Hv as (?&Hv&Heq); eauto.
              apply select_fselect in Heq. rewrite Heq, ac_fselect.
              assert (depends_on Γ cy (causl a0) (Bauto (clo a0) (ini0, oth) states)) as Hdep2.
              { eapply depends_on_incl. 3:econstructor; solve_Exists.
                1,2:intros * Has; inv Has; simpl_In; eauto with senv. }
              eapply Hsc in Hv. 4,5:eauto with senv. 2,3:eauto with senv.
              eapply sem_clock_det in Hv. 2:eapply H22.
              rewrite <-Hv, Hac; eauto using depends_on_def_last.
              eapply sem_clock_select. rewrite <-Hac; eauto using depends_on_def_last.
            + destruct H1 as (?&Hselect). rewrite Hselect in Hv.
              eapply sem_var_fselect_inv in Hv as (?&Hv&Heq). rewrite Heq, ac_fselect.
              assert (depends_on Γ cy cx (Bauto (clo a0) (ini0, oth) states)) as Hdep2.
              { eapply depends_on_incl. 3:econstructor; solve_Exists.
                1,2:intros * Has; inv Has; simpl_In; eauto with senv. }
              eapply Hsc in Hv. 4,5:eauto with senv. 2,3:eauto with senv.
              eapply sem_clock_det in Hv. 2:eapply H22.
              rewrite <-Hv, Hac; eauto using depends_on_def_last.
              eapply sem_clock_select. rewrite <-Hac; eauto using depends_on_def_last.
          - intros ? Hin' Hdep. apply HenvP. solve_In.
            eapply depends_on_incl. 3:econstructor; solve_Exists.
            1,2:intros * Has; inv Has; simpl_In; eauto with senv.
          - intros; simpl in *; destruct_conjs; split; simpl_Forall; inv_VarsDefined;
              eauto using Sem.sem_transitions_refines.
            eapply sem_block_ck'_refines; eauto.
            eapply NoDupLocals_incl; [|eauto]. etransitivity; eauto. rewrite <-H27; eauto using incl_concat.
          - intros; simpl in *; destruct_conjs; split; simpl_Forall; inv_VarsDefined.
            + eapply sem_block_ck'_restrict; eauto.
              eapply NoDupLocals_incl; [|eauto]. etransitivity; eauto. rewrite <-H28; eauto using incl_concat.
            + eapply Sem.sem_transitions_restrict; eauto. simpl_Forall; eauto with lclocking.
          - intros; simpl in *. destruct_conjs.
            rewrite <-and_assoc. split; [|auto].
            assert (Forall (fun blks => (forall y xs, VarsDefined blks xs -> In y xs -> HasCaus Γ0 y cy ->
                                              sc_var_inv Γ0 Hi0 (fselectb e k stres bs) cy)
                                     /\ sem_block_ck' (cy::envP) Hi0 (fselectb e k stres bs) blks) l0) as Hf.
            { simpl_Forall. inv_VarsDefined.
              edestruct H with (Γ:=Γ0) (xs:=xs1). 10:eauto. all:eauto.
              - eapply NoDup_locals_inv; eauto.
              - etransitivity; eauto using incl_concat.
                take (Permutation _ _) and now rewrite it.
              - intros * Hin' Hdep. eapply H32; eauto. solve_Exists.
              - intros * Hin' Hdep. eapply H33; eauto.
                2:solve_Exists. solve_In.
              - split; eauto.
                intros * Hdef' Hin' Hca. eapply H21; eauto.
                eapply VarsDefined_det in Hdef; eauto. now rewrite <-Hdef.
            } clear H.
            split.
            + intros * Hinxs Hca. inv_VarsDefined.
              rewrite <-H37 in Hinxs. apply in_concat in Hinxs as (?&?&?); inv_VarsDefined; simpl_Forall.
              eapply H21; eauto.
            + simpl_Forall; eauto.
        } clear H H25.
        split.
        + intros * Hinxs Hca1.
          assert (Syn.Is_defined_in y (Bauto ck (ini0, oth) states)) as Hdef.
          { eapply VarsDefined_Is_defined; eauto. econstructor; eauto.
            eapply NoDupLocals_incl; [|econstructor; eauto]. auto. }
          assert (Is_defined_in Γ cy (Bauto ck (ini0, oth) states)) as Hdef' by (eauto using Is_defined_in_Is_defined_in).
          eapply sc_var_inv_unselect with (tn:=List.length states) (sc:=stres) (Γ':=map (fun '(x, e) => (x, ann_with_clock e Cbase)) Γ); eauto.
          1:{ destruct states; try congruence. simpl; lia. }
          1:{ eapply sem_automaton_wt_state in H23; eauto. 1,3,4:simpl_Forall; auto.
              - inv H12. simpl_Forall; auto.
              - specialize (Hf k). destruct_conjs. simpl_Forall.
                inv H3; destruct_conjs; eauto.
              - now rewrite <-H10, <-fst_InMembers. }
          1:{ intros * Hca Hck.
              eapply HasCaus_snd_det in Hca1; eauto; [|simpl_app; eauto using NoDup_app_l]; subst.
              inv Hck. inv Hca.
              split; econstructor; solve_In; auto.
          }
          1:{ intros * Hca Hck.
              eapply HasCaus_snd_det in Hca1; eauto; [|simpl_app; eauto using NoDup_app_l]; subst.
              inv Hck. inv Hca. eapply NoDupMembers_det in H0; eauto. subst.
              assert (clo e = ck) as Heq; [|rewrite Heq].
              { inv Hdef. rename H3 into Hdef. simpl_Exists.
                simpl_Forall.
                destruct s. eapply wc_scope_Is_defined_in in H19; eauto.
                2:{ intros; simpl in *; simpl_Exists; simpl_Forall.
                    eapply wc_block_Is_defined_in; eauto. }
                eapply InMembers_In in H19 as (?&Hin').
                edestruct H16 as (Hck&_); eauto with senv.
                inv Hck. eapply NoDupMembers_det in H; eauto. congruence.
              }
              rewrite <-Hac; auto.
          }
          2:{ intros * Hnin. eapply NoDup_HasCaus_HasLastCaus; eauto. solve_NoDup_app. }
          intros * Hin. rewrite <-H10 in Hin. simpl_In. simpl_Forall.
          specialize (Hf k); destruct_conjs.
          esplit; split; [|split]; eauto.
          1:{ intros ? Hca.
              eapply HasCaus_snd_det in Hca1; eauto; [|simpl_app; eauto using NoDup_app_l]; subst.
              destruct s. eapply sem_scope_defined2; eauto.
              inv H1; econstructor; eauto; simpl_Forall; eauto using sem_block_ck'_sem_block.
          }
          eapply H0; eauto. inv Hca1; econstructor; solve_In. auto.
        + econstructor; eauto. simpl_Forall.
          specialize (Hf k); destruct_conjs; eauto.

      - (* locals *)
        eapply sc_scope in H7 as (?&?); eauto with lcaus.
        + split; eauto. constructor; eauto.
        + intros. simpl_Forall. inv_VarsDefined.
          eapply sem_block_ck'_refines; eauto.
          eapply NoDupLocals_incl; [|eauto]. etransitivity; eauto. rewrite <-H11; eauto using incl_concat.
        + intros. simpl_Forall. inv_VarsDefined.
          eapply sem_block_ck'_restrict; eauto.
          eapply NoDupLocals_incl; [|eauto]. etransitivity; eauto. rewrite <-H11; eauto using incl_concat.
        + intros.
          assert (Forall (fun blks => (forall y xs, VarsDefined blks xs -> In y xs -> HasCaus Γ0 y cy -> sc_var_inv Γ0 Hi0 bs cy)
                                     /\ sem_block_ck' (cy::envP) Hi0 bs blks) blocks) as Hf.
            { simpl_Forall. inv_VarsDefined.
              edestruct H with (xs:=xs1). 10:eauto. all:eauto.
              - eapply NoDup_locals_inv; eauto.
              - etransitivity; eauto using incl_concat.
                take (Permutation _ _) and now rewrite it.
              - intros * Hin' Hdep. eapply H16; eauto. solve_Exists.
              - intros * Hin' Hdep. eapply H17; eauto.
                2:solve_Exists. solve_In.
              - split; eauto.
                intros * Hdef' Hin' Hca. eapply H8; eauto.
                eapply VarsDefined_det in Hdef; eauto. now rewrite <-Hdef.
            }
            split; simpl_Forall; eauto.
            intros * Hin Hca. destruct_conjs. rewrite <-H18 in Hin. apply in_concat in Hin as (?&?&?).
            inv_VarsDefined; simpl_Forall; eauto.
    Qed.

    Lemma sem_node_sc_vars :
      forall n H b,
        wc_global G ->
        wt_node G n ->
        wc_node G n ->
        node_causal n ->
        Env.dom H (map fst (n_in n ++ n_out n)) ->
        Forall (sc_var_inv (senv_of_inout (n_in n ++ n_out n)) (H, @Env.empty _) b) (map snd (idcaus (n_in n))) ->
        Sem.sem_block G (H, @Env.empty _) b (n_block n) ->
        sc_vars (senv_of_inout (n_in n ++ n_out n)) (H, @Env.empty _) b /\
        sem_block_ck' (map snd (idcaus (n_in n ++ n_out n) ++ idcaus_of_locals (n_block n)))
                      (H, @Env.empty _) b (n_block n).
    Proof.
      intros * HwcG Hwtn Hwcn Hcau Hdom Hins Hsem.
      assert (Forall (sc_var_inv (senv_of_inout (n_in n ++ n_out n)) (H, @Env.empty _) b)
                     (map snd (idcaus (n_in n ++ n_out n) ++ idcaus_of_locals (n_block n))) /\
                sem_block_ck' (map snd (idcaus (n_in n ++ n_out n) ++ idcaus_of_locals (n_block n)))
                              (H, @Env.empty _) b (n_block n)) as (?&?).
      2:{ split; auto.
          change (@nil (ident * clock)) with (idck (idty (@nil (ident * (type * clock * ident))))).
          eapply sc_var_inv_sc_vars; simpl; auto with datatypes.
          - rewrite fst_NoDupMembers, map_fst_senv_of_inout, <-fst_NoDupMembers. apply n_nodup.
          - intros * Hv. inv Hv. apply InMembers_In in H2 as (?&?); simpl_In.
            eapply Env.dom_use in Hdom as (_&(?&?)). solve_In.
            do 2 esplit; eauto. reflexivity.
          - intros * Hv. inv Hv. simpl_In. congruence.
          - rewrite idcaus_of_senv_inout. eapply Forall_incl; eauto.
            solve_incl_app. }
      eapply node_causal_ind; eauto.
      - intros ?? Hperm (Hvars&Hlocs). split. rewrite <-Hperm; auto.
        eapply sem_block_ck'_Perm; eauto.
      - split; auto. apply sem_block_sem_block_ck'; auto.
      - intros ?? Hin (Hvars&Hlocs) Hdep.
        pose proof (n_defd n) as (?&Hdef&Hperm).
        pose proof (n_nodup n) as (Hnd1&Hnd2).
        destruct Hcau as (Hnd&_).
        eapply sc_block in Hlocs as (Hsc&?); eauto.
        + split; auto. constructor; auto.
          repeat rewrite idcaus_app, map_app, in_app_iff in Hin.
          rewrite or_assoc in Hin. destruct Hin as [Hin|[Hin|Hin]].
          * eapply Forall_forall in Hins; eauto.
          * simpl_In. eapply Hsc; eauto. rewrite Hperm; solve_In; eauto.
            econstructor. solve_In; eauto with datatypes. simpl; eauto. auto.
          * rewrite map_app in *.
            split; intros * Hca; exfalso; inv Hca; simpl_In.
            1,2:eapply NoDup_app_In in Hnd; eauto. 2,4:solve_In.
            1,2:eapply Hnd; simpl; solve_In. congruence.
        + rewrite idcaus_of_senv_inout; auto.
        + rewrite fst_NoDupMembers, map_fst_senv_of_inout, <-fst_NoDupMembers. apply n_nodup.
        + rewrite map_fst_senv_of_inout. apply n_nodup.
        + rewrite map_fst_senv_of_inout, Hperm. solve_incl_app.
        + eapply Hwtn.
        + unfold senv_of_inout, idck. erewrite map_map, map_ext. eapply Hwcn.
          intros; destruct_conjs; auto.
        + eapply Hwcn.
        + rewrite map_fst_senv_of_inout; eauto using Env.dom_dom_ub.
        + intros * Hil. inv Hil. simpl_In. congruence.
        + intros * [Hca|Hca] Hdep'; inv Hca; simpl_In; try congruence.
          eapply Forall_forall in Hvars; [|eapply Hdep]; eauto.
    Qed.

    Lemma sem_clocks_det' : forall H H' b ins vins ss,
        wc_env (map (fun '(x, (_, ck, _)) => (x, ck)) ins) ->
        Forall2 (sem_var H) (idents ins) vins ->
        Forall2 (sem_var H') (idents ins) vins ->
        Forall2 (fun xc => sem_clock H b (snd xc)) (map (fun '(x, (_, ck, _)) => (x, ck)) ins) ss ->
        Forall2 (fun xs => sem_clock H' b (snd xs)) (map (fun '(x, (_, ck, _)) => (x, ck)) ins) ss.
    Proof.
      intros * Hwc Hi1 Hi2 Hck.
      eapply sem_clocks_det in Hck; eauto.
      rewrite map_app.
      apply Forall_app; split; eapply Forall_impl; eauto; intros [? ?] ?.
      1,2:eapply wc_clock_incl; eauto.
      1,2:apply incl_appl; reflexivity.
    Qed.

    Lemma sem_node_restrict {prefs2} : forall (n : @node PSyn prefs2) H b xs ys,
        wc_block G (senv_of_inout (n_in n ++ n_out n)) (n_block n) ->
        Forall2 (sem_var H) (idents (n_in n)) xs ->
        Forall2 (sem_var H) (idents (n_out n)) ys ->
        Sem.sem_block G (H, Env.empty _) b (n_block n) ->
        let H' := Env.restrict H (idents (n_in n ++ n_out n)) in
        Env.dom H' (idents (n_in n ++ n_out n)) /\
        Forall2 (sem_var H') (idents (n_in n)) xs /\
        Forall2 (sem_var H') (idents (n_out n)) ys /\
        Sem.sem_block G (H', Env.empty _) b (n_block n).
    Proof with eauto.
      intros * Hwc Hins Houts Heqs.
      remember (Env.restrict _ _) as H'; simpl.
      repeat split.
      - subst. eapply Env.dom_lb_restrict_dom.
        apply Env.dom_lb_intro. intros x Hin.
        unfold idents in *.
        repeat rewrite map_app in Hin. repeat rewrite in_app_iff in Hin. destruct Hin as [Hin|Hin].
        + apply sem_vars_In in Hins. rewrite Forall_forall in Hins...
        + apply sem_vars_In in Houts. rewrite Forall_forall in Houts...
      - eapply Forall2_impl_In; [|eauto]; intros. simpl_In.
        eapply sem_var_restrict; eauto.
        eapply in_map_iff; do 2 esplit; eauto using in_or_app. reflexivity.
      - eapply Forall2_impl_In; [|eauto]; intros. simpl_In.
        eapply sem_var_restrict; eauto.
        eapply in_map_iff; do 2 esplit; eauto using in_or_app. reflexivity.
      - subst. unfold idents. eapply Sem.sem_block_restrict in Heqs; eauto with lclocking.
        rewrite map_fst_senv_of_inout in Heqs; auto.
    Qed.

    Lemma sc_var_inv_intro {prefs2} : forall (n : @node PSyn prefs2) H xs,
        node_causal n ->
        Forall2 (sem_var H) (idents (n_in n)) xs ->
        Forall2 (fun xc => sem_clock H (clocks_of xs) (snd xc)) (map (fun '(x, (_, ck, _)) => (x, ck)) (n_in n)) (map abstract_clock xs) ->
        Forall (sc_var_inv (senv_of_inout (n_in n ++ n_out n)) (H, Env.empty _) (clocks_of xs)) (map snd (idcaus (n_in n))).
    Proof.
      intros * (Hnd&_) Hvar Hclock.
      unfold idents, idck, idty, idcaus in *.
      simpl_Forall.
      eapply Forall2_ignore2 in Hclock. simpl_Forall.
      split; intros * Hca Hck Hv; simpl in *; inv Hca; inv Hck; simpl_In; try congruence.
      eapply NoDupMembers_det in Hin0; eauto; inv_equalities. 2:apply n_nodup.
      rewrite map_app in Hnd.
      eapply NoDup_app_l, NoDup_snd_det in Hnd. 2:solve_In.
      2:clear Hin; rewrite map_app, in_app_iff; left; solve_In. subst.
      specialize (node_NoDup n) as Hnd. apply fst_NoDupMembers in Hnd.
      eapply NoDupMembers_det in Hnd; auto.
      2:eapply in_or_app, or_introl, H0. 2:eauto. inv_equalities.
      eapply sem_var_det in H2; eauto. now rewrite H2.
    Qed.

    Fact wc_exp_Is_free_left : forall Γ e x k,
        wc_exp G Γ e ->
        Is_free_left Γ x k e ->
        In x (map snd (idcaus_of_senv Γ)).
    Proof.
      Local Ltac solve_forall_exists :=
        match goal with
        | H: Is_free_left_list _ _ _ _ |- _ =>
            eapply Is_free_left_list_Exists in H as (?&?)
        end; simpl_Exists; simpl_Forall; eauto.
      induction e using exp_ind2; intros * Hwc Hfree;
        inv Hwc; inv Hfree; eauto.
      - (* var *) solve_In. 2:eapply idcaus_of_senv_In; eauto. auto.
      - (* last *) solve_In. 2:eapply idcaus_of_senv_In; eauto. auto.
      - (* binop *) destruct H1; eauto.
      - (* fby *)
        solve_forall_exists.
      - (* arrow *)
        destruct H3 as [Hex|Hex]; eauto; solve_forall_exists.
      - (* when *)
        destruct H2 as [[? Hex]|Hex]; subst; eauto.
        + solve_In. 2:eapply idcaus_of_senv_In; eauto. auto.
        + solve_forall_exists.
      - (* merge *)
        destruct H2 as [[? Hex]|Hex]; subst; eauto.
        + solve_In. 2:eapply idcaus_of_senv_In; eauto. auto.
        + simpl_Exists. simpl_Forall.
          solve_forall_exists.
      - (* case *)
        destruct H3 as [[? Hex]|[Hex|(?&?&Hex)]]; subst; eauto.
        + simpl_Exists. simpl_Forall.
          solve_forall_exists.
        + specialize (H11 _ eq_refl). solve_forall_exists.
      - (* app *)
        destruct H13 as [(?&Hex)|Hex]; eauto.
        1,2:simpl_Exists; simpl_Forall; eauto.
    Qed.

    (** After getting sc_var_inv, we can easily give an alignment lemma for expressions *)
    Lemma sc_exp'' : forall Γ Γty H b e vs,
        wc_global G ->
        NoDupMembers Γ ->
        sc_vars Γ H b ->

        wt_exp G Γty e ->
        wc_exp G Γ e ->
        Sem.sem_exp G H b e vs ->
        Forall2 (sem_clock (fst H) b) (clockof e) (map abstract_clock vs).
    Proof.
      intros * HwcG Hnd1 Hinv Hwt Hwc Hsem.
      eapply sc_vars_sc_var_inv in Hinv; eauto.
      assert (forall k, k < numstreams e -> sc_exp_inv Γ Γty H b e k); intros.
      eapply exp_causal_ind
             with (P_exp:=sc_exp_inv _ _ H b); eauto with lclocking; intros.
      - apply sc_exp_const.
      - apply sc_exp_enum.
      - eapply sc_exp_var; eauto.
      - eapply sc_exp_last; eauto.
      - apply sc_exp_unop; auto.
      - apply sc_exp_binop; auto.
      - apply sc_exp_fby; auto.
      - apply sc_exp_arrow; auto.
      - eapply sc_exp_when; eauto.
      - eapply sc_exp_merge; eauto.
      - apply sc_exp_case; auto.
      - eapply sc_exp_app; eauto.
      - eapply Forall_forall in Hinv; eauto.
        eapply wc_exp_Is_free_left; eauto.
      - assert (length vs = numstreams e) as Hlen'.
        { eapply sem_exp_numstreams in Hsem; eauto with lclocking. }
        eapply Forall2_forall2; split.
        + rewrite map_length.
          rewrite length_clockof_numstreams; auto.
        + intros ? ? ? ? ? Hlen Hnth1 Hnth2; subst.
          rewrite length_clockof_numstreams in Hlen.
          specialize (H0 _ Hlen _ Hwt Hwc Hsem).
          rewrite nth_indep with (d':=Cbase). 2:rewrite length_clockof_numstreams; auto.
          erewrite map_nth'; eauto. setoid_rewrite Hlen'; auto.
    Qed.

    Corollary sc_exps'' : forall Γ Γty H b es vss,
        wc_global G ->
        NoDupMembers Γ ->
        sc_vars Γ H b ->

        Forall (wt_exp G Γty) es ->
        Forall (wc_exp G Γ) es ->
        Forall2 (Sem.sem_exp G H b) es vss ->
        Forall2 (sem_clock (fst H) b) (clocksof es) (map abstract_clock (concat vss)).
    Proof.
      intros * HwcG Hnd1 Hsc Hwt Hwc Hsem.
      unfold clocksof.
      rewrite Forall2_map_2, flat_map_concat_map.
      apply Forall2_concat. simpl_Forall.
      eapply sc_exp'' with (Γ:=Γ) in H1; eauto. simpl_Forall; eauto.
    Qed.

    Lemma sc_transitions'' Γty Γ : forall Hi bs' trans def stres,
        wc_global G ->
        NoDupMembers Γ ->
        Forall (fun '(e, _) => wt_exp G Γty e) trans ->
        Forall (fun '(e, _) => wc_exp G Γ e /\ clockof e = [Cbase]) trans ->
        sc_vars Γ Hi bs' ->
        sem_transitions G Hi bs' trans def stres ->
        abstract_clock stres ≡ bs'.
    Proof.
      induction trans; intros * HwG Hnd Hwt Hwc Hsc Hsem;
        inv Hwt; inv Hwc; inv Hsem; destruct_conjs.
      - rewrite H0, const_stres_ac. reflexivity.
      - rewrite H13. apply choose_first_ac; eauto.
        eapply sc_exp'' in H6; eauto.
        take (clockof _ = _) and rewrite it in H6. simpl in *. simpl_Forall.
        eapply sc_slower in H8; eauto using ac_aligned.
        apply slower_nth; intros * Hbs. setoid_rewrite Str_nth_map.
        apply slower_nth with (n:=n) in H8; auto.
        apply bools_of_nth with (n:=n) in H7 as [(Hv&Hx)|[(Hv&Hx)|(?&Hx)]].
        + setoid_rewrite H8 in Hv; congruence.
        + setoid_rewrite H8 in Hv; congruence.
        + rewrite Hx; auto.
    Qed.

  End sc_inv.

  Lemma sc_vars_mask : forall Γ H b r k,
      sc_vars Γ H b ->
      sc_vars Γ (Sem.mask_hist k r H) (maskb k r b).
  Proof.
    intros * (Hinv1&Hinv2). unfold Sem.mask_hist.
    split; intros; [edestruct Hinv1 as (?&?&?)|edestruct Hinv2 as (?&?&?)]; eauto;
      take (sem_var _ _ _) and rename it into Hvar;
      take (sem_clock _ _ _ _) and rename it into Hck.
    1,2:eapply sem_var_mask in Hvar; eapply sem_clock_mask in Hck.
    1,2:do 2 esplit; eauto; try rewrite ac_mask; eauto.
  Qed.

  Lemma sc_vars_ffilter ck e sc : forall Γ Γ' Hi Hl bs,
      sem_clock Hi bs ck (abstract_clock sc) ->
      (forall x ck', HasClock Γ' x ck' -> HasClock Γ x ck /\ ck' = Cbase) ->
      (forall x, IsLast Γ' x -> IsLast Γ x) ->
      sc_vars Γ (Hi, Hl) bs ->
      sc_vars Γ' (ffilter_hist e sc Hi, ffilter_hist e sc Hl) (ffilterb e sc bs).
  Proof.
    intros * Hsemck Hcks Hlasts (Hsc1&Hsc2).
    split; intros.
    - edestruct Hcks as (?&?); eauto; subst.
      edestruct Hsc1 as (?&Hvar&Hck); eauto. eapply sem_var_ffilter in Hvar; eauto.
      do 2 esplit; eauto.
      eapply sem_clock_det in Hck. 2:eapply Hsemck. rewrite ac_ffilter, <-Hck.
      eapply sem_clock_filter; eauto.
    - edestruct Hcks as (?&?); eauto; subst.
      edestruct Hsc2 as (?&Hvar&Hck); eauto. eapply sem_var_ffilter in Hvar.
      do 2 esplit; eauto.
      eapply sem_clock_det in Hck. 2:eapply Hsemck. rewrite ac_ffilter, <-Hck.
      eapply sem_clock_filter; eauto.
  Qed.

  Lemma sc_vars_fselect ck e k sc : forall Γ Γ' Hi Hl bs,
      sem_clock Hi bs ck (abstract_clock sc) ->
      (forall x ck', HasClock Γ' x ck' -> HasClock Γ x ck /\ ck' = Cbase) ->
      (forall x, IsLast Γ' x -> IsLast Γ x) ->
      sc_vars Γ (Hi, Hl) bs ->
      sc_vars Γ' (fselect_hist e k sc Hi, fselect_hist e k sc Hl) (fselectb e k sc bs).
  Proof.
    intros * Hsemck Hcks Hlasts (Hsc1&Hsc2).
    split; intros.
    - edestruct Hcks as (?&?); eauto; subst.
      edestruct Hsc1 as (?&Hvar&Hck); eauto. eapply sem_var_fselect in Hvar; eauto.
      do 2 esplit; eauto.
      eapply sem_clock_det in Hck. 2:eapply Hsemck. unfold fselectv, fselect.
      rewrite ac_mask, ac_ffilter, <-Hck.
      eapply sem_clock_select; eauto.
    - edestruct Hcks as (?&?); eauto; subst.
      edestruct Hsc2 as (?&Hvar&Hck); eauto. eapply sem_var_fselect in Hvar.
      do 2 esplit; eauto.
      eapply sem_clock_det in Hck. 2:eapply Hsemck. unfold fselectv, fselect.
      rewrite ac_mask, ac_ffilter, <-Hck.
      eapply sem_clock_select; eauto.
  Qed.

  Lemma sc_vars_unmask : forall Γ H b r,
      (forall k, sc_vars Γ (Sem.mask_hist k r H) (maskb k r b)) ->
      sc_vars Γ H b.
  Proof.
    intros * Hinv.
    split; intros.
    - assert (Hinv0:=Hinv 0). edestruct Hinv0 as ((?&?&?)&_); eauto.
      take (sem_var _ _ _) and eapply sem_var_mask_inv in it as (vs&Hvar0&Heq0).
      exists vs; split; auto.
      eapply sem_clock_unmask; intros k; rewrite <-ac_mask.
      specialize (Hinv k) as ((?&?&?)&_); eauto.
      take (sem_var (mask_hist _ _ _) _ _) and eapply sem_var_mask_inv in it as (?&?&Heqk).
      eapply sem_var_det in Hvar0; eauto.
      rewrite <-Hvar0, <-Heqk; auto.
    - assert (Hinv0:=Hinv 0). edestruct Hinv0 as (_&(?&?&?)); eauto.
      take (sem_var _ _ _) and eapply sem_var_mask_inv in it as (vs&Hvar0&Heq0).
      exists vs; split; auto.
      eapply sem_clock_unmask; intros k; rewrite <-ac_mask.
      specialize (Hinv k) as (_&(?&?&?)); eauto.
      take (sem_var (mask_hist _ _ _) _ _) and eapply sem_var_mask_inv in it as (?&?&Heqk).
      eapply sem_var_det in Hvar0; eauto.
      rewrite <-Hvar0, <-Heqk; auto.
  Qed.

  Lemma sc_vars_slower_hist : forall Γ H b,
      sc_vars Γ H b ->
      Env.dom (fst H) (map fst Γ) ->
      slower_hist (fst H) b.
  Proof.
    intros * (Hsc&_) Hdom ?? Hfind.
    assert (exists e, In (x, e) Γ) as (?&Hin).
    { eapply Env.find_In, Env.dom_use in Hfind; eauto. simpl_In; eauto. }
    edestruct Hsc as (?&Hv&Hck). econstructor; solve_In; eauto.
    eapply sem_var_det in Hv.
    2:{ econstructor; eauto. reflexivity. }
    rewrite <-Hv in Hck.
    eapply sc_slower; eauto. eapply ac_aligned.
  Qed.

  (** Second step of the proof:
      Give clocked semantics for expressions, equations and blocks,
      given that all named streams are aligned with their clocks
   *)
  Section sem_ck.
    Context {PSyn : block -> Prop}.
    Context {prefs : PS.t}.
    Variable (G : @global PSyn prefs).

    Hypothesis HwcG : wc_global G.

    Hypothesis Hnode : forall f ins outs,
        sem_node G f ins outs ->
        sem_clock_inputs G f ins ->
        sem_node_ck G f ins outs.

    Lemma sem_exp_sem_exp_ck : forall Γ Γty H bs e vs,
        NoDupMembers Γ ->
        NoDup (map snd (idcaus_of_senv Γ)) ->
        sc_vars Γ H bs ->
        wt_exp G Γty e ->
        wc_exp G Γ e ->
        Sem.sem_exp G H bs e vs ->
        sem_exp_ck G H bs e vs.
    Proof.
      induction e using exp_ind2; intros * Hnd1 Hnd3 Hsc Hwt Hwc Hsem;
        inv Hwt; inv Hwc; inv Hsem;
          econstructor; eauto.
      1-5,10-11:(eapply Forall2_impl_In; [|eauto]; intros;
                 rewrite Forall_forall in *; eauto).
      - (* merge *)
        eapply Forall2Brs_impl_In; [|eauto]; intros ?? Hin Hse.
        simpl_Exists; simpl_Forall; eauto.
      - (* case *)
        eapply Forall2Brs_impl_In; [|eauto]; intros ?? Hin Hse.
        simpl_Exists; simpl_Forall; eauto.
      - (* case *)
        eapply Forall2Brs_impl_In; [|eauto]; intros ?? Hin Hse.
        simpl_Exists; simpl_Forall; eauto.
      - (* case (default) *)
        simpl in *.
        specialize (H23 _ eq_refl). specialize (H25 _ eq_refl).
        simpl_Forall; eauto.
      - (* app *)
        intros k. eapply Hnode; eauto.
        specialize (H26 k). inv H26. rewrite H15 in H3; inv H3.
        repeat (esplit; eauto).
        eapply sc_inside_mask with (es:=es); eauto.
        + eapply sem_exps_sem_var; eauto.
        + eapply wc_find_node in HwcG as (?&?&?); eauto.
        + eapply sc_exps'' with (Γ:=Γ); eauto.
    Qed.

    Corollary sem_equation_sem_equation_ck : forall Γ Γty H bs equ,
        NoDupMembers Γ ->
        NoDup (map snd (idcaus_of_senv Γ)) ->
        sc_vars Γ H bs ->
        wt_equation G Γty equ ->
        wc_equation G Γ equ ->
        Sem.sem_equation G H bs equ ->
        sem_equation_ck G H bs equ.
    Proof.
      intros * Hnd1 Hnd2 Hsc Hwt Hwc Hsem.
      inv Hsem. inv Hwt. inv Hwc.
      - (* app *)
        econstructor; eauto.
        apply Forall_singl in H0. inv H0.
        inv H1; inv H14. inv H5. do 2 (econstructor; eauto).
        + eapply Forall2_impl_In; [|eauto]; intros.
          eapply sem_exp_sem_exp_ck with (Γ:=Γ); eauto. 1-2:eapply Forall_forall; [|eauto]; eauto.
        + eapply Forall2_impl_In; [|eauto]; intros.
          eapply sem_exp_sem_exp_ck with (Γ:=Γ); eauto. 1-2:eapply Forall_forall; [|eauto]; eauto.
        + intros k. eapply Hnode; eauto.
          specialize (H28 k). inv H28. rewrite H1 in H17; inv H17. rewrite H1 in H8; inv H8.
          repeat (esplit; eauto).
          eapply sc_inside_mask with (es:=es0); eauto.
          * eapply sem_exps_sem_var; eauto.
          * eapply wc_find_node in HwcG as (?&?&?); eauto.
          * eapply sc_exps'' with (Γ:=Γ); eauto.
      - (* general case *)
        econstructor; eauto.
        eapply Forall2_impl_In; [|eauto]; intros.
        eapply sem_exp_sem_exp_ck with (Γ:=Γ); eauto. 1-2:eapply Forall_forall; eauto.
    Qed.

    Corollary sem_transitions_sem_transitions_ck : forall Γ Γty H bs trans def stres,
        NoDupMembers Γ ->
        NoDup (map snd (idcaus_of_senv Γ)) ->
        sc_vars Γ H bs ->
        Forall (fun '(e, _) => wt_exp G Γty e) trans ->
        Forall (fun '(e, _) => wc_exp G Γ e) trans ->
        Sem.sem_transitions G H bs trans def stres ->
        sem_transitions_ck G H bs trans def stres.
    Proof.
      induction trans; intros * Hnd1 Hnd2 Hsc Hwt Hwc Hsem; inv Hwt; inv Hwc; inv Hsem;
        econstructor; eauto using sem_exp_sem_exp_ck.
    Qed.

    Lemma sc_vars_subclock Γ Γ' : forall Hi bs bs' ck,
        sem_clock (fst Hi) bs ck bs' ->
        (forall x ck', HasClock Γ' x ck' -> HasClock Γ x ck /\ ck' = Cbase) ->
        (forall x, IsLast Γ' x -> IsLast Γ x) ->
        sc_vars Γ Hi bs ->
        sc_vars Γ' Hi bs'.
    Proof.
      intros * Hsemck Hck Hla (Hinv1&Hinv2).
      split; intros * Hasck.
      - edestruct Hck as (Hasck'&?); eauto; subst.
        edestruct Hinv1 as (?&Hv&Hsemck'); eauto. do 2 esplit; eauto.
        eapply sem_clock_det in Hsemck; eauto.
        constructor. symmetry; auto.
      - intros Hl. edestruct Hck as (Hasck'&?); eauto; subst.
        edestruct Hinv2 as (?&Hv&Hsemck'); eauto. do 2 esplit; eauto.
        eapply sem_clock_det in Hsemck; eauto. constructor; symmetry; auto.
    Qed.

    Hint Resolve Env.union_refines2 Env.union_dom' Env.adds_opt'_refines Env.adds_opt'_dom
         EqStrel EqStrel_Reflexive : core.

    Fact idcaus_of_senv_filter_NoDup : forall ck Γ,
        NoDup (map snd (idcaus_of_senv Γ)) ->
        NoDup (map snd (idcaus_of_senv (map_filter (fun '(x, e0) => if clo e0 ==b ck then Some (x, ann_with_clock e0 Cbase) else None) Γ))).
    Proof.
      intros * Hnd.
      unfold idcaus_of_senv in *. simpl_app.
      apply NoDup_app'; [apply NoDup_app_l in Hnd|apply NoDup_app_r in Hnd|].
      - induction Γ as [|(?&?)]; simpl; auto. inv Hnd.
        destruct (_ ==b _); simpl; auto. constructor; auto.
        contradict H1. solve_In.
        destruct (_ ==b _) eqn:Heq; inv Hf; rewrite equiv_decb_equiv in Heq; inv Heq; simpl in *; auto.
      - induction Γ as [|(?&?)]; simpl in *; auto.
        destruct (_ ==b _); simpl in *; (destruct (causl_last a); simpl in *; [inv Hnd|]); auto.
        constructor; auto.
        contradict H1. simpl_In.
        destruct (_ ==b _) eqn:Heq; inv Hf; rewrite equiv_decb_equiv in Heq; inv Heq; simpl in *.
        solve_In; try rewrite Hf0; simpl; eauto. auto.
      - simpl_Forall. intros contra. simpl_In.
        destruct (clo a1 ==b _) eqn:Heq; inv Hf; try rewrite equiv_decb_equiv in Heq; inv Heq; simpl in *.
        destruct (_ ==b _) eqn:Heq; inv Hf1; try rewrite equiv_decb_equiv in Heq; inv Heq; simpl in *.
        eapply NoDup_app_In; eauto. 2:solve_In; rewrite Hf0; simpl; eauto.
        clear Hin. solve_In.
    Qed.

    Lemma sem_scope_sem_scope_ck {A} f_idcaus P_nd P_vd P_wt P_wc P_blk1 (P_blk2: _ -> _ -> Prop) :
      forall envP locs (blk: A) xs Γty Γck H bs,
        NoDupMembers Γty ->
        NoDupMembers Γck ->
        NoDup (map snd (idcaus_of_senv Γck ++ idcaus_of_scope f_idcaus (Scope locs blk))) ->
        VarsDefinedScope P_vd (Scope locs blk) xs ->
        NoDupScope P_nd (map fst Γty) (Scope locs blk) ->
        incl xs (map fst Γck) ->
        (forall x ty, HasType Γck x ty -> HasType Γty x ty) ->
        incl (map snd (idcaus_of_senv Γck ++ idcaus_of_scope f_idcaus (Scope locs blk))) envP ->
        Env.dom (fst H) (map fst Γty) ->
        sc_vars Γck H bs ->
        wt_scope P_wt G Γty (Scope locs blk) ->
        wc_env (idck Γck) ->
        wc_scope P_wc G Γck (Scope locs blk) ->
        sem_scope_ck' G P_blk1 envP H bs (Scope locs blk) ->
        (forall Γ xs Hi Hi' Hl,
            P_vd blk xs ->
            P_nd Γ blk ->
            incl xs Γ ->
            Env.refines (@EqSt _) Hi Hi' -> P_blk1 (Hi, Hl) blk -> P_blk1 (Hi', Hl) blk) ->
        (forall Γty Γck xs Hi Hl,
            P_vd blk xs ->
            P_nd Γty blk ->
            incl xs (map fst Γck) ->
            incl (map fst Γck) Γty ->
            P_wc Γck blk ->
            P_blk1 (Hi, Hl) blk -> P_blk1 (Env.restrict Hi (map fst Γck), Hl) blk) ->
        (forall xs Γ Hi,
            incl xs Γ ->
            P_vd blk xs ->
            P_nd Γ blk ->
            P_blk1 Hi blk ->
            Env.dom_lb (fst Hi) xs) ->
        (forall xs Γty Γck Hi,
            NoDupMembers Γty ->
            NoDupMembers Γck ->
            NoDup (map snd (idcaus_of_senv Γck ++ f_idcaus blk)) ->
            P_vd blk xs ->
            P_nd (map fst Γty) blk ->
            incl xs (map fst Γck) ->
            (forall x ty, HasType Γck x ty -> HasType Γty x ty) ->
            incl (map snd (idcaus_of_senv Γck ++ f_idcaus blk)) envP ->
            Env.dom (fst Hi) (map fst Γty) ->
            sc_vars Γck Hi bs ->
            P_wt Γty blk ->
            wc_env (idck Γck) ->
            P_wc Γck blk ->
            P_blk1 Hi blk ->
            P_blk2 Hi blk) ->
        sem_scope_ck (fun Hi => sem_exp_ck G Hi bs) P_blk2 H bs (Scope locs blk).
    Proof.
      intros * Hnd1 Hnd2 Hnd3 Hvd Hnd4 Hincl Hincl1 HenvP Hdom Hsc Hwt Hwenv Hwc Hsem Href Hres Hdom' Hind;
        inv Hvd; inv Hnd4; inv Hwt; inv Hwc; inv Hsem.
      assert (incl (map fst Γck) (map fst Γty)) as Hincl1'.
      { intros ? Hin. simpl_In. assert (HasType Γck a a0.(typ)) as Hty by eauto with senv.
        apply Hincl1 in Hty. inv Hty. solve_In. }
      assert (Env.dom_lb Hi' (map fst locs)) as Hdomlb.
      { eapply Env.dom_lb_incl. 2:eapply Hdom' in H18. 4,5:eauto. all:eauto.
        solve_incl_app. apply incl_appl'. etransitivity; eauto. }
      assert (Env.refines (EqSt (A:=svalue)) Hi (Env.restrict (Env.union Hi Hi') (map fst Γty ++ map fst locs))) as Href1.
      { intros ?? Hfind.
        assert (In x (map fst Γty)) as Hin by (eapply Env.dom_use; eauto; econstructor; eauto).
        destruct (Env.find x Hi') eqn:Hfind2.
        - do 2 esplit. 2:eapply Env.restrict_find, Env.union_find3'; eauto using in_or_app.
          eapply sem_var_det. econstructor; [eapply Hfind|reflexivity].
          eapply H4; eauto. econstructor; eauto; reflexivity.
          intro contra. eapply H6; eauto using in_or_app.
        - do 2 esplit. reflexivity.
          eapply Env.restrict_find, Env.union_find2; eauto using in_or_app. }
      assert (NoDupMembers (Γck ++ senv_of_locs locs)) as Hnd2'.
      { apply NoDupMembers_app; auto.
        - now apply NoDupMembers_senv_of_locs.
        - intros * Hinm1 Hinm2. rewrite InMembers_senv_of_locs in Hinm2.
          eapply H6; eauto. apply Hincl1', fst_InMembers; auto.
      }

      assert (sc_vars (Γck ++ senv_of_locs locs)
                      (Env.restrict (Env.union Hi Hi') (map fst Γty ++ map fst locs), Hl') bs
             ) as Hsc'.
      { apply sc_vars_app; eauto using sc_vars_refines.
        - intros * Hinm. eapply NoDupMembers_app_InMembers in Hnd2'; eauto.
        - eapply sc_var_inv_sc_vars.
          + apply NoDupMembers_senv_of_locs; auto.
          + intros * Hv. inv Hv. apply fst_InMembers in H; simpl_In.
            eapply Env.dom_lb_use in Hdomlb as (?&Hfind); eauto. 2:solve_In.
            do 2 eexists; try reflexivity.
            eapply Env.restrict_find, Env.union_find3'; eauto.
            apply in_or_app, or_intror; solve_In.
          + intros * Hv. inv Hv. simpl_In. destruct o as [(?&?)|]; simpl in *; try congruence.
            edestruct H15 as (?&?&?&?&?&?&?); eauto.
          + simpl_Forall.
            assert (In i0 envP) as HinP.
            { eapply HenvP.
              rewrite 2 map_app, 2 in_app_iff. right; left. solve_In. }
            simpl_Forall.
            take (sc_var_inv _ _ _ _) and destruct it as (Hsc1'&Hsc2').
            split; intros * Hca Hck Hv.
            1,2:eapply sem_clock_refines'. 3:eapply Hsc1'; eauto.
            6:eapply Hsc2'; eauto.
            * inv Hck. simpl_In. eapply Forall_forall in H9; [|solve_In; eauto]; simpl in *.
              eapply wc_clock_wx_clock in H9; eauto.
            * intros * Hin Hv'. inv Hin. rewrite fst_InMembers, map_app, map_fst_senv_of_locs in H0.
              eapply sem_var_restrict; eauto.
              rewrite in_app_iff in *. destruct H0; eauto.
            * eapply sem_var_restrict_inv in Hv as (?&?); eauto.
            * inv Hck. simpl_In. eapply Forall_forall in H9; [|solve_In; eauto]; simpl in *.
              eapply wc_clock_wx_clock in H9; eauto.
            * intros * Hin Hv'. inv Hin. rewrite fst_InMembers, map_app, map_fst_senv_of_locs in H0.
              eapply sem_var_restrict; eauto.
              rewrite in_app_iff in *. destruct H0; eauto.
      }
      assert (Env.dom (Env.restrict (Env.union Hi Hi') (map fst Γty ++ map fst locs)) (map fst Γty ++ map fst locs)) as Hdom''.
      { eapply Env.dom_lb_restrict_dom, Env.union_dom_lb; eauto using Env.dom_dom_lb. }

      eapply Sscope with (Hi':=Env.restrict (Env.union Hi Hi') (map fst Γty ++ map fst locs)); eauto.
      - intros * Hvar Hnin1.
        apply sem_var_restrict_inv in Hvar as (Hin&Hvar). apply sem_var_union in Hvar as [|Hvar]; auto.
      - eapply local_hist_dom; eauto.
      - intros. edestruct H15; destruct_conjs; eauto.
        do 3 esplit. repeat split; eauto using sem_var_refines.
        + simpl_Forall.
          rewrite <-map_fst_senv_of_locs, <-map_app.
          eapply sem_exp_sem_exp_ck with (Γ:=Γck ++ _), Sem.sem_exp_restrict, Sem.sem_exp_refines; eauto using Env.union_refines4'.
          * clear - Hnd3. rewrite idcaus_of_senv_app. solve_NoDup_app.
          * rewrite map_app, map_fst_senv_of_locs; auto.
          * eauto with ltyping.
        + eapply sem_var_restrict, sem_var_refines; eauto using Env.union_refines4'.
          apply in_app_iff, or_intror. solve_In.
      - clear - Hsc'. destruct Hsc' as (Hsc1&Hsc2).
        setoid_rewrite IsLast_app in Hsc2.
        setoid_rewrite HasClock_app in Hsc1. setoid_rewrite HasClock_app in Hsc2.
        split; eauto.
      - eapply Hind with (Γty:=Γty++_); eauto.
        + apply NoDupMembers_app; auto.
          * apply NoDupMembers_senv_of_locs; auto.
          * intros * Hinm1 Hinm2. rewrite InMembers_senv_of_locs in Hinm2.
            eapply H6; eauto. apply fst_InMembers; auto.
        + clear - Hnd3. simpl in *.
          rewrite idcaus_of_senv_app.
          simpl_app. auto.
        + rewrite map_app, map_fst_senv_of_locs; auto.
        + rewrite map_app, map_fst_senv_of_locs. now apply incl_appl'.
        + intros *. rewrite 2 HasType_app. intros [|]; auto.
        + etransitivity; [|eauto].
          rewrite idcaus_of_senv_app. simpl_app. reflexivity.
        + rewrite map_app, map_fst_senv_of_locs. eapply Env.dom_lb_restrict_dom.
          eapply Env.union_dom_lb; eauto using Env.dom_dom_lb.
        + simpl_app. eapply Forall_app; split; eauto.
          * eapply Forall_impl; [|eauto]; intros; simpl in *.
            eapply wc_clock_incl; [|eauto]. solve_incl_app.
          * simpl_Forall; eauto.
        + rewrite <-map_fst_senv_of_locs, <-map_app.
          eapply Href. 1,2:eauto. apply incl_appl'; etransitivity; eauto.
          eapply Env.incl_restrict_refines; eauto using EqStrel_Transitive.
          2:eapply Hres, Href. 2-3,6-8,10-11:eauto using Env.union_refines4'.
          all:repeat rewrite map_app; repeat rewrite map_fst_senv_of_locs; apply incl_appl'; auto.
          etransitivity; eauto.
    Qed.

    Lemma sem_block_sem_block_ck : forall envP blk xs Γty Γck H bs,
        NoDupMembers Γty ->
        NoDupMembers Γck ->
        NoDup (map snd (idcaus_of_senv Γck ++ idcaus_of_locals blk)) ->
        VarsDefined blk xs ->
        NoDupLocals (map fst Γty) blk ->
        incl xs (map fst Γck) ->
        (forall x ty, HasType Γck x ty -> HasType Γty x ty) ->
        incl (map snd (idcaus_of_senv Γck ++ idcaus_of_locals blk)) envP ->
        Env.dom (fst H) (map fst Γty) ->
        sc_vars Γck H bs ->
        wt_block G Γty blk ->
        wc_env (idck Γck) ->
        wc_block G Γck blk ->
        sem_block_ck' G envP H bs blk ->
        sem_block_ck G H bs blk.
    Proof.
      induction blk using block_ind2;
        intros * Hnd1 Hnd2 Hnd5 Hvars Hnd6 Hincl Hincl1 HenvP Hdom Hsc Hwt Hwenv Hwc Hsem;
        inv Hnd6; inv Hvars; inv Hwt; inv Hwc; inv Hsem; simpl_ndup Hnd1.

      - (* equation *)
        constructor. eapply sem_equation_sem_equation_ck with (Γ:=Γck); eauto.
        rewrite app_nil_r in Hnd5; auto.

      - (* reset *)
        econstructor; eauto.
        + assert (Hsem2:=H7).
          eapply sem_exp_sem_exp_ck with (Γ:=Γck) in Hsem2; eauto.
          rewrite map_app in Hnd5; eauto using NoDup_app_l.
        + intros k. specialize (H15 k). simpl_Forall. inv_VarsDefined.
          eapply H with (Γty:=Γty); eauto.
          * eapply NoDup_locals_inv; eauto.
          * etransitivity; eauto using incl_concat.
          * etransitivity; [|eauto]. rewrite 2 map_app. apply incl_appr'.
            intros ??. solve_In.
          * eapply Env.dom_map; eauto.
          * eapply sc_vars_mask; eauto.

      - (* switch *)
        assert (sem_clock (fst H0) bs ck (abstract_clock sc)) as Hsemck.
        { eapply sc_exp'' with (Γ:=Γck) in H16; eauto.
          take (clockof _ = _) and rewrite it in H16; simpl_Forall; eauto.
        }
        assert (incl (map fst Γck) (map fst Γty)) as Hincl'.
        { intros ? Hv. simpl_In. assert (HasType Γck a a0.(typ)) as Hty by eauto with senv.
          specialize (Hincl1 _ _ Hty). inv Hincl1. do 2 esplit; eauto. auto. }

        econstructor; eauto.
        + eapply sem_exp_sem_exp_ck with (Γ:=Γck) in H16; eauto.
          solve_NoDup_app.
        + simpl_Forall.
          destruct H0 as (Hfilter1&Hfilter2).
          apply filter_hist_ffilter_hist in Hfilter1.
          do 2 esplit; eauto.
          1:{ instantiate (1:=(_, _)). split; simpl; eauto.
              take (wt_streams _ _) and rewrite H7 in it. apply Forall2_singl in it.
              eapply filter_hist_restrict_ac with (xs:=map fst Γ'); eauto.
              intros * Hin Hvar. simpl_In.
              destruct Hsc as ((?&Hv&Hck)&_). eapply H15; eauto with senv.
              eapply sem_var_det in Hvar; eauto. rewrite <-Hvar.
              eapply sem_clock_det in Hsemck; eauto.
          }
          destruct s. eapply sem_scope_restrict; eauto.
          1:{ apply Forall_forall. intros * Hin; simpl_In.
              edestruct H15 as (?&Hbase); eauto with senv. rewrite Hbase. constructor. }
          2:{ intros; simpl_Forall. eapply sem_block_restrict; eauto. }
          eapply sem_scope_sem_scope_ck
            with (Γty:=Γty)
                 (Γck:=map_filter (fun '(x, e) => if e.(clo) ==b ck then Some (x, ann_with_clock e Cbase) else None) Γck); eauto.
          * eapply nodupmembers_map_filter; eauto.
            intros *. destruct (_ ==b _); simpl; auto.
          * subst. eapply NoDup_locals_inv2; eauto.
            rewrite map_app in *. eapply NoDup_incl_app2. 3:apply Hnd5.
            -- intros ? Hin. unfold idcaus_of_senv in *. rewrite map_app, in_app_iff in *.
               destruct Hin; [left|right]; simpl_In; destruct (_ ==b _) eqn:Heq; inv Hf; rewrite equiv_decb_equiv in Heq; inv Heq; simpl in *.
               1,2:solve_In; try rewrite Hf0; simpl; eauto. auto.
            -- intros Hnd. eapply idcaus_of_senv_filter_NoDup; eauto.
          * intros ? Hin.
            eapply VarsDefinedScope_Is_defined with (P_def:=Exists (Syn.Is_defined_in a)) in H6; eauto.
            2:{ eapply NoDupScope_incl ; [| |eauto]. 2:etransitivity; eauto using incl_concat.
                intros; simpl in *; simpl_Forall. eauto using NoDupLocals_incl. }
            2:{ intros; simpl in *. inv_VarsDefined. eapply Forall_VarsDefined_Is_defined; eauto.
                simpl_Forall. 1,2:now rewrite Hperm. }
            eapply wc_scope_Is_defined_in, InMembers_In in H6 as (?&?); eauto.
            2:{ intros; simpl in *. eapply Exists_Is_defined_in_wx_In; [|eauto].
                simpl_Forall; eauto with lclocking. }
            edestruct H15; eauto with senv. inv H6. solve_In.
            2:rewrite equiv_decb_refl; eauto. auto.
          * subst. intros * Hty. apply Hincl1.
            inv Hty. simpl_In.
            destruct (_ ==b _) eqn:Heq; inv Hf; rewrite equiv_decb_equiv in Heq. eauto with senv.
          * subst. etransitivity; [|eapply HenvP].
            rewrite 2 map_app. apply incl_app; [apply incl_appl|apply incl_appr; intros ??; solve_In].
            unfold idcaus_of_senv. simpl_app. repeat rewrite map_map.
            apply incl_app; [apply incl_appl|apply incl_appr].
            1-2:intros ??; solve_In. 1,3:destruct (_ ==b _); inv Hf; eauto; simpl in *. rewrite Hf0; simpl; eauto. auto.
          * apply Env.dom_map. auto.
          * eapply sc_vars_morph, sc_vars_ffilter with (Γ:=Γck); eauto. 2:reflexivity.
            -- split; try reflexivity. rewrite <-Hfilter2; reflexivity.
            -- subst. intros * Hck. inv Hck; simpl_In.
               destruct (_ ==b _) eqn:Heq; inv Hf; rewrite equiv_decb_equiv in Heq; inv Heq.
               eauto with senv.
            -- subst. intros * Hca. inv Hca; simpl_In.
               destruct (_ ==b _) eqn:Heq; inv Hf; rewrite equiv_decb_equiv in Heq; inv Heq.
               eauto with senv.
          * subst. eapply Forall_forall; intros ? Hin. simpl_In.
            destruct (_ ==b _) eqn:Heq; inv Hf; rewrite equiv_decb_equiv in Heq; inv Heq.
            constructor.
          * eapply wc_scope_incl; [| |eauto|].
            1,2:intros * Hin.
            -- eapply H15 in Hin as (Hck&?); subst.
               inv Hck. econstructor; solve_In; auto. simpl. rewrite equiv_decb_refl; eauto. auto.
            -- assert (exists ck, HasClock Γ' x ck) as (?&Hck) by (inv Hin; eauto with senv).
               eapply H15 in Hck as (Hck&?); subst.
               eapply H17 in Hin as Hil; subst.
               inv Hil. inv Hck. eapply NoDupMembers_det in H0; eauto; subst.
               econstructor; solve_In; auto. simpl. rewrite equiv_decb_refl; eauto. auto.
            -- intros; simpl in *; simpl_Forall; eauto using wc_block_incl.
          * eapply sem_scope_ck'_refines1. 2-5:eauto.
            etransitivity; eauto.
                      * intros; simpl in *; simpl_Forall; inv_VarsDefined. eapply sem_block_ck'_refines; eauto.
            eapply NoDupLocals_incl; [|eauto]. etransitivity; eauto. rewrite <-H25; eauto using incl_concat.
          * intros; simpl in *; simpl_Forall; inv_VarsDefined. eapply sem_block_ck'_restrict; eauto.
            eapply NoDupLocals_incl; [|eauto]. do 2 (etransitivity; eauto). rewrite <-H26; eauto using incl_concat.
          * intros; simpl in *; simpl_Forall; inv_VarsDefined.
            destruct Hi. eapply Forall_sem_block_dom_lb; eauto; simpl_Forall; eauto using NoDupLocals_incl, sem_block_ck'_sem_block.
          * intros; simpl in *; simpl_Forall. inv_VarsDefined.
            eapply H with (Γty:=Γty0); eauto using NoDup_locals_inv.
            -- etransitivity; eauto. rewrite <-H34; eauto using incl_concat.
            -- etransitivity; eauto. rewrite 2 map_app. apply incl_appr'. intros ??; solve_In.

      - (* automaton *)
        assert (sc_vars (map_filter (fun '(x, e) => if clo e ==b ck then Some (x, ann_with_clock e Cbase) else None) Γck) H0 bs') as Hsc'.
        { eapply sc_vars_subclock. 1,4:eauto.
          - intros * Hck; inv Hck; simpl_In.
            destruct (_ ==b _) eqn:Heq; inv Hf. rewrite equiv_decb_equiv in Heq; inv Heq.
            eauto with senv.
          - intros * Hl; inv Hl; simpl_In.
            destruct (_ ==b _) eqn:Heq; inv Hf. rewrite equiv_decb_equiv in Heq; inv Heq.
            eauto with senv.
        }
        assert (bs' ≡ abstract_clock stres) as Hac.
        { symmetry. eapply sc_transitions'' with (Γ:=map_filter (fun '(x, e) => if e.(clo) ==b ck then Some (x, ann_with_clock e Cbase) else None) Γck) in H24; eauto. 3,4:simpl_Forall; eauto.
          - apply ac_fby1 in H25. now rewrite <-H25.
          - apply nodupmembers_map_filter; auto.
            intros; destruct (_ ==b _); simpl; auto.
          - split; auto.
            eapply wc_exp_incl; [| |eauto].
            + intros * Has. eapply H17 in Has as (Has&?).
              inv Has. econstructor. solve_In; simpl. rewrite equiv_decb_refl; eauto.
              auto.
            + intros * His. eapply H18 in His as His'.
              inv His; inv His'. edestruct H17 as (Has&?); eauto with senv.
              inv Has. eapply NoDupMembers_det in H21; eauto; subst.
              econstructor. solve_In; simpl. rewrite equiv_decb_refl; eauto.
              simpl; auto.
        }
        assert (incl (map fst Γck) (map fst Γty)) as Hincl'.
        { intros ? Hv. simpl_In. assert (HasType Γck a a0.(typ)) as Hty by eauto with senv.
          specialize (Hincl1 _ _ Hty). inv Hincl1. do 2 esplit; eauto. auto. }

        econstructor; eauto.
        + eapply sem_transitions_sem_transitions_ck with (Γ:=map_filter (fun '(x, e) => if e.(clo) ==b ck then Some (x, ann_with_clock e Cbase) else None) Γck); eauto. 3,4:simpl_Forall; eauto.
          * apply nodupmembers_map_filter; auto.
            intros; destruct (_ ==b _); simpl; auto.
          * rewrite map_app in Hnd5. apply idcaus_of_senv_filter_NoDup; eauto using NoDup_app_l.
          * eapply wc_exp_incl; [| |eauto].
            -- intros * Has. eapply H17 in Has as (Has&?).
               inv Has. econstructor. solve_In; simpl. rewrite equiv_decb_refl; eauto.
               auto.
            -- intros * His. eapply H18 in His as His'.
               inv His; inv His'. edestruct H17 as (Has&?); eauto with senv.
               inv Has. eapply NoDupMembers_det in H21; eauto; subst.
               econstructor. solve_In; simpl. rewrite equiv_decb_refl; eauto.
               simpl; auto.
        + simpl_Forall. specialize (H26 k); destruct_conjs.
          destruct H0 as (Hsel1&Hsel2).
          apply select_hist_fselect_hist in Hsel1.
          eapply sc_vars_fselect with (Γ':=map_filter (fun '(x, e) => if e.(clo) ==b ck then Some (x, ann_with_clock e Cbase) else None) Γck) in Hsc as Hsc''.
          2:rewrite <-Hac; eauto.
          2:{ intros * Has. inv Has; simpl_In. destruct (_ ==b _) eqn:Heq; inv Hf; rewrite equiv_decb_equiv in Heq; inv Heq.
              eauto with senv. }
          2:{ intros * Has. inv Has; simpl_In. destruct (_ ==b _) eqn:Heq; inv Hf; rewrite equiv_decb_equiv in Heq; inv Heq.
              eauto with senv. }
          esplit; split.
          1:{ instantiate (1:=(_, _)). split; simpl; eauto.
              eapply select_hist_restrict_ac with (xs:=map fst Γ'); eauto.
              intros * Hin Hvar. simpl_In.
              destruct Hsc as ((?&Hv&Hck)&_). eapply H17; eauto with senv.
              eapply sem_var_det in Hvar; eauto. rewrite <-Hvar.
              eapply sem_clock_det in H23; eauto. rewrite H23; auto.
          }
          destruct s as [?(?&?)]. eapply sem_scope_restrict; eauto.
          1:{ apply Forall_forall. intros * Hin; simpl_In.
              edestruct H17 as (?&Hbase); eauto with senv. rewrite Hbase. constructor. }
          2:{ intros; destruct_conjs; split; simpl_Forall; eauto using sem_block_restrict.
              eapply sem_transitions_restrict; eauto. simpl_Forall; eauto with lclocking. }
          eapply sem_scope_sem_scope_ck
                 with (Γty:=Γty) (Γck:=map_filter (fun '(x, e) => if e.(clo) ==b ck then Some (x, ann_with_clock e Cbase) else None) Γck); eauto.
          * subst. eapply nodupmembers_map_filter; eauto.
            intros *. destruct (_ ==b _); simpl; auto.
          * subst. eapply NoDup_locals_inv2; eauto.
            rewrite map_app in *. eapply NoDup_incl_app2. 3:apply Hnd5.
            -- intros ? Hin. unfold idcaus_of_senv in *. rewrite map_app, in_app_iff in *.
               destruct Hin; [left|right]; simpl_In; destruct (_ ==b _) eqn:Heq; inv Hf; rewrite equiv_decb_equiv in Heq; inv Heq; simpl in *.
               1,2:solve_In; try rewrite Hf0; simpl; eauto. auto.
            -- intros Hnd. eapply idcaus_of_senv_filter_NoDup; eauto.
          * intros ? Hin.
            eapply VarsDefinedScope_Is_defined with (P_def:=fun blks => Exists (Syn.Is_defined_in a) (fst blks)) in H7; eauto.
            2:{ eapply NoDupScope_incl ; [| |eauto]. 2:etransitivity; eauto using incl_concat.
                intros; simpl in *; simpl_Forall. eauto using NoDupLocals_incl. }
            2:{ intros; simpl in *. inv_VarsDefined. eapply Forall_VarsDefined_Is_defined; eauto.
                simpl_Forall. 1,2:now rewrite Hperm. }
            eapply wc_scope_Is_defined_in, InMembers_In in H7 as (?&?); eauto.
            2:{ intros; simpl in *. eapply Exists_Is_defined_in_wx_In; [|eauto].
                simpl_Forall; eauto with lclocking. }
            edestruct H17; eauto with senv. inv H4. solve_In.
            2:rewrite equiv_decb_refl; eauto. auto.
          * subst. intros * Hty. apply Hincl1.
            inv Hty. simpl_In.
            destruct (_ ==b _) eqn:Heq; inv Hf; rewrite equiv_decb_equiv in Heq. eauto with senv.
          * subst. etransitivity; [|eapply HenvP].
            rewrite 2 map_app. apply incl_app; [apply incl_appl|apply incl_appr; intros ??; solve_In].
            unfold idcaus_of_senv. simpl_app. repeat rewrite map_map.
            apply incl_app; [apply incl_appl|apply incl_appr].
            1-2:intros ??; solve_In. 1,3:destruct (_ ==b _); inv Hf; eauto; simpl in *. rewrite Hf0; simpl; eauto. auto.
          * apply Env.dom_map. auto.
          * eapply sc_vars_morph; eauto. 2:reflexivity.
            split; try reflexivity. rewrite <-Hsel2; reflexivity.
          * subst. eapply Forall_forall; intros ? Hin. simpl_In.
            destruct (_ ==b _) eqn:Heq; inv Hf; rewrite equiv_decb_equiv in Heq; inv Heq.
            constructor.
          * eapply wc_scope_incl; [| |eauto|].
            1,2:intros * Hin.
            -- eapply H17 in Hin as (Hck&?); subst.
               inv Hck. econstructor; solve_In; auto. simpl. rewrite equiv_decb_refl; eauto. auto.
            -- assert (exists ck, HasClock Γ' x ck) as (?&Hck) by (inv Hin; eauto with senv).
               eapply H17 in Hck as (Hck&?); subst.
               eapply H18 in Hin as Hil; subst.
               inv Hil. inv Hck. eapply NoDupMembers_det in H0; eauto; subst.
               econstructor; solve_In; auto. simpl. rewrite equiv_decb_refl; eauto. auto.
            -- intros; simpl in *; destruct_conjs; split; simpl_Forall; eauto using wc_block_incl.
               split; eauto using wc_exp_incl.
          * eapply sem_scope_ck'_refines2. 2-5:eauto.
            etransitivity; eauto.
          * intros; simpl in *; destruct_conjs; split; simpl_Forall; inv_VarsDefined; eauto using Sem.sem_transitions_refines.
            eapply sem_block_ck'_refines; eauto.
            eapply NoDupLocals_incl; [|eauto]. etransitivity; eauto. rewrite <-H26; eauto using incl_concat.
          * intros; simpl in *; destruct_conjs; split; simpl_Forall; inv_VarsDefined.
            -- eapply sem_block_ck'_restrict; eauto.
               eapply NoDupLocals_incl; [|eauto]. do 2 (etransitivity; eauto). rewrite <-H28; eauto using incl_concat.
            -- eapply Sem.sem_transitions_restrict; eauto. simpl_Forall; eauto with lclocking.
          * intros; simpl in *; simpl_Forall; inv_VarsDefined.
            destruct Hi. eapply Forall_sem_block_dom_lb; eauto; simpl_Forall; eauto using NoDupLocals_incl, sem_block_ck'_sem_block.
          * intros; simpl in *; destruct_conjs; split.
            2:{ eapply sem_transitions_sem_transitions_ck; eauto.
                2,3:simpl_Forall; eauto. solve_NoDup_app. }
            simpl_Forall. inv_VarsDefined.
            eapply H with (Γty:=Γty0); eauto using NoDup_locals_inv.
            -- etransitivity; eauto. rewrite <-H37; eauto using incl_concat.
            -- etransitivity; eauto. rewrite 2 map_app. apply incl_appr'. intros ??; solve_In.

      - (* locals *)
        constructor.
        eapply sem_scope_sem_scope_ck with (Γty:=Γty); eauto.
        + intros; simpl in *. simpl_Forall. inv_VarsDefined.
          eapply sem_block_ck'_refines; eauto.
          eapply NoDupLocals_incl; [|eauto]. etransitivity; eauto. rewrite <-H12; eauto using incl_concat.
        + intros; simpl in *. simpl_Forall. inv_VarsDefined.
          eapply sem_block_ck'_restrict; eauto.
          eapply NoDupLocals_incl; [|eauto]. do 2 (etransitivity; eauto). rewrite <-H13; eauto using incl_concat.
        + intros; simpl in *. inv_VarsDefined.
          destruct Hi.
          eapply Forall_sem_block_dom_lb; eauto;
            simpl_Forall; eauto using NoDupLocals_incl, sem_block_ck'_sem_block.
        + intros; simpl in *. simpl_Forall. inv_VarsDefined.
          eapply H with (Γty:=Γty0); eauto.
          * eapply NoDup_locals_inv; eauto.
          * etransitivity; eauto.
            rewrite <-H21; eauto using incl_concat.
          * etransitivity; eauto.
            rewrite 2 map_app. apply incl_appr'.
            intros ??; solve_In.
    Qed.

  End sem_ck.

  Theorem sem_node_sem_node_ck {PSyn prefs} :
    forall (G : @global PSyn prefs),
      wt_global G ->
      wc_global G ->
      Forall node_causal (nodes G) ->
      forall f ins outs,
        Sem.sem_node G f ins outs ->
        sem_clock_inputs G f ins ->
        sem_node_ck G f ins outs.
  Proof with eauto.
    intros (enums&nodes) Hwt Hwc.
    assert (Ordered_nodes (Global enums nodes)) as Hord by (eauto using wl_global_Ordered_nodes with ltyping).
    revert Hwc Hord.
    induction nodes; intros Hwc Hord Hcaus ??? Hsem Hckins. now inversion Hsem.
    assert (Hsem' := Hsem).
    inversion_clear Hsem' as [? ? ? ? ? ? Hfind Hins Houts Heqs Hbk].
    pose proof (Lord.find_node_not_Is_node_in _ _ _ Hord Hfind) as Hnini.
    simpl in Hfind. destruct (ident_eq_dec (n_name a) f).
    - destruct Hckins as (?&?&Hfind'&Hins'&Hscin).
      rewrite find_node_now in Hfind'; auto. inv Hfind'.
      rewrite find_node_now in Hfind; auto. inv Hfind.
      eapply Sem.sem_block_cons in Heqs; eauto.
      assert (Hord':=Hord). inversion_clear Hord' as [|? ? Hord'' Hnneqs Hnn].
      inversion_clear Hwc as [|?? (Hwcn&_) Hwcg].
      inv Hcaus.
      assert (Hwcn':=Hwcn). destruct Hwcn' as (?&?&?).

      (* sem_clock H0 -> sem_clock H *)
      eapply sem_clocks_det' in Hscin; eauto. clear x Hins'.

      (* restrict H *)
      eapply sem_node_restrict in Heqs as (Hdom&Hins'&Houts'&Heqs'); eauto.
      remember (Env.restrict H (idents (n_in n ++ n_out n))) as H'.
      eapply sem_clocks_det with (ins:=n_out n) in Hscin; eauto. 2:rewrite Permutation_app_comm; eauto.
      clear H HeqH' Hins Houts.

      (* sc_vars H *)
      assert (wc_global (Global enums nodes0)) as Hvars by eauto.
      eapply sem_node_sc_vars in Hvars as (Hvars&Hloc); eauto.
      2:{ intros. eapply IHnodes; eauto. inv Hwt. inv H7. constructor; auto. }
      2:{ inv Hwt; inv H5; destruct H8; auto. }
      2:{ eapply sc_var_inv_intro; eauto. }

      (* sem_node_ck *)
      pose proof (n_defd n) as (?&Hdef&Hperm).
      eapply sem_block_sem_block_ck in Hloc; eauto; auto with datatypes.
      eapply Snode with (H:=H'); eauto.
      + rewrite find_node_now; auto.
      + eapply sem_block_ck_cons'; eauto.
      + unfold clocked_node. split; auto.
        rewrite map_fst_senv_of_inout; auto.
      + intros. eapply IHnodes; eauto. inv Hwt; inv H7; constructor; auto.
      + rewrite fst_NoDupMembers, map_fst_senv_of_inout, <-fst_NoDupMembers. apply n_nodup.
      + rewrite fst_NoDupMembers, map_fst_senv_of_inout, <-fst_NoDupMembers. apply n_nodup.
      + simpl. destruct H2 as (Hnd&_). rewrite idcaus_of_senv_inout. auto.
      + rewrite map_fst_senv_of_inout. apply n_nodup.
      + rewrite map_fst_senv_of_inout, Hperm. solve_incl_app.
      + simpl. rewrite idcaus_of_senv_inout. reflexivity.
      + rewrite map_fst_senv_of_inout; auto.
      + inv Hwt; inv H5; destruct H8 as ((?&?&?&?)&_); auto.
      + unfold senv_of_inout. simpl_app.
        erewrite 2 map_map, map_ext, map_ext with (l:=n_out n); eauto.
        1,2:intros; destruct_conjs; auto.

    - rewrite find_node_other in Hfind; eauto.
      eapply Sem.sem_node_cons in Hsem; auto.
      assert (Hord':=Hord). rewrite cons_is_app in Hord'.
      inv Hord'. inv Hwt; inv H1. inv Hwc. inv Hcaus. eapply IHnodes in Hsem; eauto.
      eapply sem_node_ck_cons'; eauto.
      constructor; auto.
      eapply sem_clock_inputs_cons; eauto.
  Qed.

  (** ** Finally getting the alignment result from sem_exp_ck *)

  Lemma sc_outside_mask' {PSyn prefs} :
    forall (G: @global PSyn prefs) f n H b Γ ncks es rs ss vs bck sub,
      wc_global G ->
      find_node f G = Some n ->
      Forall (wc_exp G Γ) es ->
      Forall2 (sem_exp_ck G H b) es ss ->
      (forall k, sem_node_ck G f (map (maskv k rs) (concat ss)) (map (maskv k rs) vs)) ->
      Forall2 (fun '(_, o) (s : Stream svalue) => LiftO True (fun x0 : ident => sem_var (fst H) x0 s) o) ncks vs ->
      Forall2 (sem_clock (fst H) b) (clocksof es) (map abstract_clock (concat ss)) ->
      Forall2 (WellInstantiated bck sub) (map (fun '(x, (_, ck, _)) => (x, ck)) (n_in n)) (nclocksof es) ->
      Forall2 (WellInstantiated bck sub) (map (fun '(x, (_, ck, _)) => (x, ck)) (n_out n)) ncks ->
      Forall2 (sem_clock (fst H) b) (map fst ncks) (map abstract_clock vs).
  Proof.
    intros * HwcG Hfind Hwc Hseme Hsem Hvars Hcki Hwi Hwo.
    eapply sc_outside_mask with (rs:=rs) (es:=es); eauto.
    2,3:eapply wc_find_node in HwcG as (?&?&?&?); eauto.
    - eapply sem_exps_sem_var, sem_exps_ck_sem_exps; eauto.
    - intros k.
      specialize (Hsem k). inv Hsem. rewrite Hfind in H1; inv H1.
      exists H0. repeat split; eauto.
      destruct H6 as (?&Hinv). clear - H3 Hinv. destruct Hinv as (Hinv&_).
      unfold idents, idck, idty in *. simpl_Forall.
      edestruct Hinv as (?&Hvar'&Hck); eauto.
      econstructor; simpl_app; try (rewrite in_app_iff; right; solve_In). auto.
      simpl in *.
      eapply sem_var_det in H2; eauto. rewrite <-H2; eauto.
  Qed.

  Fact sc_exps' {PSyn prefs} : forall (G : @global PSyn prefs) H b Γ es ss,
      Forall
         (fun e => forall vs,
              wc_exp G Γ e ->
              sem_exp_ck G H b e vs ->
              Forall2 (sem_clock (fst H) b) (clockof e) (map abstract_clock vs)) es ->

      Forall (wc_exp G Γ) es ->
      Forall2 (sem_exp_ck G H b) es ss ->
      Forall2 (sem_clock (fst H) b) (clocksof es) (map abstract_clock (concat ss)).
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
                          Forall2 (sem_clock (fst H) b) (clockof e) (map abstract_clock vs)) (snd es)) es ->
    Forall (fun es => Forall (wc_exp G Γ) (snd es)) es ->
    Forall (fun '(i, es) => Forall (eq (Con ck x (tx, i))) (clocksof es)) es ->
    Forall2Brs (sem_exp_ck G H b) es vs ->
    Forall (Forall (fun '(i, v) => sem_clock (fst H) b (Con ck x (tx, i)) (abstract_clock v))) vs.
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
      (* NoDupMembers Γ -> *)
      sc_vars Γ H b ->
      wc_exp G Γ e ->
      sem_exp_ck G H b e vs ->
      Forall2 (sem_clock (fst H) b) (clockof e) (map abstract_clock vs).
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
      destruct Hinv as ((?&?&?)&_). econstructor; solve_In; eauto.
      eapply sem_var_det in H7; eauto. rewrite <-H7; auto.
    - (* last *)
      constructor; auto.
      destruct Hinv as (_&(?&?&?)); eauto.
      eapply sem_var_det in H8; eauto. rewrite <-H8; auto.
    - (* unop *)
      eapply IHe in H8; eauto. rewrite H4 in H8; simpl in H8.
      rewrite <-ac_lift1; eauto.
    - (* binop *)
      eapply IHe1 in H9; eauto. rewrite H6 in H9; simpl in H9.
      rewrite <-ac_lift2; eauto.
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
      clear - H14 H15 H0. revert tys H0.
      repeat setoid_rewrite Forall2_map_1.
      induction H15; intros * Hsem; simpl in *; inv Hsem; constructor; eauto.
      eapply sc_when; eauto.
    - (* merge *)
      simpl_Forall.
      assert (length vs0 = length tys) as Hlen1.
      { eapply Forall2Brs_length1 in H15.
        2:{ simpl_Forall. eapply sem_exp_numstreams; eauto using sem_exp_ck_sem_exp with lclocking. }
        destruct es as [|(?&?)]; try congruence. simpl in *.
        inv H15; simpl in *.
        inv H8. rewrite H9, length_clocksof_annots; auto.
      }
      assert (Hlen2:=H15). eapply Forall2Brs_length2 in Hlen2.
      eapply Forall2Brs_sc_exp1 in H15; eauto.
      eapply Forall2_forall2 in H16 as (Hlen3&Hmerge).
      eapply Forall2_forall2; split; auto; intros.
      setoid_rewrite <-Hlen3. congruence.
      eapply sc_merge in Hmerge. 1,3:eauto. 4,5:eauto. 3:simpl in *; congruence.
      + eapply Forall_forall in Hlen2; [|eapply nth_In; rewrite Hlen1; eauto].
        instantiate (1:=[]). instantiate (1:=[]) in Hlen2.
        destruct (nth n vs0 []), es; simpl in *; try congruence; auto.
      + eapply Forall_forall in H15; [|eapply nth_In]; eauto.
        eapply Forall_impl; [|eauto]; intros (?&?) ?; eauto.
        setoid_rewrite Hlen1; auto.
    - (* case *)
      assert (length vs0 = length tys) as Hlen1.
      { eapply Forall2Brs_length1 in H21.
        2:{ simpl_Forall. eapply sem_exp_numstreams; eauto using sem_exp_ck_sem_exp with lclocking. }
        destruct es as [|(?&?)]; try congruence. simpl in *.
        inv H21; simpl in *.
        inv H11. rewrite H15, length_clocksof_annots; auto.
      }
      rewrite Forall2_map_1, Forall2_map_2.
      eapply Forall3_forall3 in H22 as (?&?&Hcase).
      eapply Forall2_forall2; split; intros.
      setoid_rewrite <-H3; congruence.
      eapply ac_case in Hcase. rewrite <-Hcase.
      3:instantiate (2:=[]). 4:instantiate (2:=None). 3-5:eauto; reflexivity. 2:rewrite Hlen1; auto.
      eapply IHe in H20; eauto.
      rewrite H7 in H20; simpl in H20. inv H20; auto.
    - (* case *)
      assert (length vs0 = length tys) as Hlen1.
      { eapply Forall2Brs_length1 in H21.
        2:{ eapply Forall_forall; intros (?&?) ?. eapply Forall_forall; intros.
            eapply sem_exp_numstreams; eauto using sem_exp_ck_sem_exp.
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
      Forall2 (sem_clock (fst H) b) (clocksof es) (map abstract_clock (concat vss)).
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
      Forall2 (sem_clock (fst H) b) (clocksof es) (map abstract_clock vss).
  Proof.
    induction es; intros * HwcG Hsc Hwc Hsem; inv Hwc; inv Hsem; simpl; auto.
    eapply sc_exp in H4; eauto. simpl in H4. inv H4; inv H8; simpl.
    constructor; eauto.
  Qed.

  Corollary sc_transitions {PSyn prefs} (G: @global PSyn prefs) Γ : forall Hi bs' trans def stres,
      wc_global G ->
      sc_vars Γ Hi bs' ->

      Forall (fun '(e, _) => wc_exp G Γ e /\ clockof e = [Cbase]) trans ->
      sem_transitions_ck G Hi bs' trans def stres ->
      abstract_clock stres ≡ bs'.
  Proof.
    induction trans; intros * HwG Hsc Hwc Hsem;
      inv Hwc; inv Hsem; destruct_conjs.
    - rewrite H0, const_stres_ac. reflexivity.
    - rewrite H11. apply choose_first_ac; eauto.
      eapply sc_exp in H4; eauto.
      take (clockof _ = _) and rewrite it in H4. simpl in *. simpl_Forall.
      eapply sc_slower in H6; eauto using ac_aligned.
      apply slower_nth; intros * Hbs. setoid_rewrite Str_nth_map.
      apply slower_nth with (n:=n) in H6; auto.
      apply bools_of_nth with (n:=n) in H5 as [(Hv&Hx)|[(Hv&Hx)|(?&Hx)]].
      + setoid_rewrite H6 in Hv; congruence.
      + setoid_rewrite H6 in Hv; congruence.
      + rewrite Hx; auto.
  Qed.

  Fact wc_global_Ordered_nodes {PSyn prefs} : forall (G: @global PSyn prefs),
      wc_global G ->
      Ordered_nodes G.
  Proof.
    intros G Hwt.
    apply wl_global_Ordered_nodes; auto with lclocking.
  Qed.

  (** ** Another version of semantics equivalence, including sem_clock_inputs *)
  Section sem_ref.
    Context {PSyn1 PSyn2 : block -> Prop}.
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
      - (* reset *)
        econstructor; eauto using sem_ref_sem_exp.
        intros k. specialize (H8 k).
        rewrite Forall_forall in *; eauto.
      - (* switch *)
        econstructor; eauto using sem_ref_sem_exp.
        simpl_Forall; do 2 esplit; eauto.
        inv H4; econstructor; eauto.
        + intros. edestruct H11 as (?&?&?&?&?&?&?); eauto.
          do 3 esplit; eauto using sem_ref_sem_exp.
        + simpl_Forall; eauto.
      - (* automaton *)
        econstructor; eauto using sem_ref_sem_transitions.
        simpl_Forall. specialize (H10 k); destruct_conjs.
        do 2 esplit; eauto.
        inv H3; econstructor; eauto.
        + intros. edestruct H12 as (?&?&?&?&?&?&?); eauto.
          do 3 esplit; eauto using sem_ref_sem_exp.
        + destruct_conjs. split; simpl_Forall; eauto using sem_ref_sem_transitions.
      - (* local *)
        constructor. inv H4; econstructor; eauto.
        + intros. edestruct H7 as (?&?&?&?&?&?&?); eauto.
          do 3 esplit; eauto using sem_ref_sem_exp.
        + simpl_Forall; eauto.
    Qed.

    Fact global_sem_ref_nil : forall enms1 enms2,
      global_sem_refines (Global enms1 []) (Global enms2 []).
    Proof.
      intros * f ins outs Hsem.
      inv Hsem. unfold find_node in H0; simpl in H0; inv H0.
    Qed.

    Fact global_sem_ref_cons : forall enms1 enms2 nds nds' n n' f,
        Ordered_nodes (Global enms1 (n::nds)) ->
        Ordered_nodes (Global enms2 (n'::nds')) ->
        n_name n = f ->
        n_name n' = f ->
        global_sem_refines (Global enms1 nds) (Global enms2 nds') ->
        node_sem_refines (Global enms1 (n::nds)) (Global enms2 (n'::nds')) f ->
        global_sem_refines (Global enms1 (n::nds)) (Global enms2 (n'::nds')).
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
      IStr.sem_var_instant (Env.map (fun _ => absent) H) x absent.
  Proof.
    intros * Var. unfold IStr.sem_var_instant in *.
    rewrite Env.Props.P.F.map_o, Var; auto.
  Qed.
  Global Hint Resolve sem_var_instant_absent : lcsem.

  Lemma sem_clock_false: forall H ck b b',
      IStr.sem_clock b H ck b' ->
      IStr.sem_clock (fun _ => false) (fun n => Env.map (fun _ => absent) (H n)) ck (fun _ => false).
  Proof.
    intros * Sem n. specialize (Sem n).
    revert Sem. generalize (b n) (b' n). clear b b'.
    induction ck; intros * Sem; inv Sem; eauto using IStr.sem_clock_instant with lcsem.
  Qed.

  Section sem_node_absent.
    Context {PSyn : block -> Prop}.
    Context {prefs : PS.t}.

    Import List.

    Lemma Forall2_sem_exp_absent: forall (f : list (Stream svalue) -> list (Stream svalue)) (G : @global PSyn prefs) H b es ss,
        Forall2 (fun e vs => sem_exp_ck G H b e (f vs)) es ss ->
        Forall2 (sem_exp_ck G H b) es (map f ss).
    Proof.
      intros * Sem. simpl_Forall; auto.
    Qed.
    Hint Resolve Forall2_sem_exp_absent : lcsem.

    Lemma sem_var_absent: forall H x v,
        sem_var H x v ->
        sem_var (Env.map (fun _ => Streams.const absent) H) x (Streams.const absent).
    Proof.
      intros * Var. inv Var.
      econstructor; eauto. 2:reflexivity.
      eapply PositiveMap.map_1 with (f:=fun _ => Streams.const absent); eauto.
    Qed.
    Hint Resolve sem_var_absent : lcsem.

    Lemma sem_var_absent_inv : forall H x v,
        sem_var (Env.map (fun _ => Streams.const absent) H) x v ->
        exists v', sem_var H x v' /\ v ≡ Streams.const absent.
    Proof.
      intros * Var. inv Var.
      unfold Env.MapsTo in *. rewrite Env.Props.P.F.map_o in H1.
      apply option_map_inv in H1 as (?&?&?); subst.
      do 2 esplit; eauto. econstructor; eauto. reflexivity.
    Qed.

    Lemma sem_clock_absent: forall H bs ck bs',
        sem_clock H bs ck bs' ->
        sem_clock (Env.map (fun _ => Streams.const absent) H) (Streams.const false) ck (Streams.const false).
    Proof.
      intros * Hck.
      rewrite sem_clock_equiv in *.
      apply sem_clock_false in Hck.
      intros n. specialize (Hck n); simpl in *.
      setoid_rewrite Env.map_map. setoid_rewrite Env.map_map in Hck.
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

    Fact clocked_node_absent: forall H Hl bs vars,
        clocked_node (H, Hl) bs vars ->
        clocked_node (Env.map (fun _ => Streams.const absent) H, Env.map (fun _ => Streams.const absent) Hl) (Streams.const false) vars.
    Proof.
      unfold clocked_node.
      intros * (Hdom&Hsc).
      split.
      - simpl. now rewrite Env.dom_map.
      - destruct Hsc as (Hsc1&Hsc2). split; intros.
        + edestruct Hsc1 as (?&?&Hck); eauto.
          exists (Streams.const absent); split; eauto using sem_var_absent.
          eapply sem_clock_absent in Hck. now rewrite ac_Streams_const.
        + edestruct Hsc2 as (?&?&Hck); eauto.
          exists (Streams.const absent); split; eauto using sem_var_absent.
          eapply sem_clock_absent in Hck. now rewrite ac_Streams_const.
    Qed.

    Fact sem_scope_absent {A} P_exp1 P_blk1 (P_exp2: _ -> _ -> _ -> Prop) (P_blk2: _ -> _ -> Prop) : forall locs (blks: A) Hi bs,
        sem_scope_ck P_exp1 P_blk1 Hi bs (Scope locs blks) ->
        (forall Hi e vs,
            P_exp1 Hi e vs ->
            P_exp2 (Env.map (fun _ : Stream svalue => Streams.const absent) (fst Hi), Env.map (fun _ : Stream svalue => Streams.const absent) (snd Hi)) e
                   (List.map (fun _ => Streams.const absent) vs)) ->
        (forall Hi,
            P_blk1 Hi blks ->
            P_blk2 (Env.map (fun _ : Stream svalue => Streams.const absent) (fst Hi), Env.map (fun _ : Stream svalue => Streams.const absent) (snd Hi)) blks) ->
        sem_scope_ck P_exp2 P_blk2
                     (Env.map (fun _ => Streams.const absent) (fst Hi), Env.map (fun _ => Streams.const absent) (snd Hi)) (Streams.const false) (Scope locs blks).
    Proof.
      intros * Hsem Hexp Hblk. inv Hsem.
      eapply Sscope with (Hi':=Env.map (fun _ => Streams.const absent) Hi'); eauto.
      - intros * Hsemv Hinm1.
        eapply sem_var_absent_inv in Hsemv as (?&Hvar&Heq).
        eapply H1 in Hvar; eauto.
        rewrite Heq. eapply sem_var_absent; eauto.
      - rewrite Env.dom_map.
        eapply Env.dom_intro. intros.
        eapply Env.dom_use in H2. rewrite H2, 2 in_app_iff.
        apply or_iff_compat_r.
        now rewrite <-2 fst_InMembers, <-2 Env.In_Members, Env.Props.P.F.map_in_iff.
      - eapply Env.refines_map; eauto. intros; reflexivity.
      - intros * Hin. edestruct H4; destruct_conjs; eauto.
        do 3 esplit. repeat split. 2,4:eapply sem_var_absent; eauto.
        2:apply fby_absent. eapply Hexp in H; eauto.
      - destruct H7 as (Hsc1&Hsc2). split; intros.
        + edestruct Hsc1 as (?&?&Hck); eauto.
          exists (Streams.const absent); split; eauto using sem_var_absent.
          eapply sem_clock_absent in Hck. now rewrite ac_Streams_const.
        + edestruct Hsc2 as (?&?&Hck); eauto.
          exists (Streams.const absent); split; eauto using sem_var_absent.
          eapply sem_clock_absent in Hck. now rewrite ac_Streams_const.
      - eapply Hblk in H8; eauto.
    Qed.

    Lemma sem_block_absent:
      forall (G : @global PSyn prefs) H bs bck,
        sem_block_ck G H bs bck ->
        sem_block_ck G (Env.map (fun _ => Streams.const absent) (fst H), Env.map (fun _ => Streams.const absent) (snd H)) (Streams.const false) bck.
    Proof with eauto with lcsem.
      intros * Sem.
      eapply sem_block_ck_ind2
        with (P_exp := fun H _ e vs => sem_exp_ck G (Env.map (fun _ => Streams.const absent) (fst H), Env.map (fun _ => Streams.const absent) (snd H))
                                                (Streams.const false) e (List.map (fun _ => Streams.const absent) vs))
             (P_equation := fun H _ eq => sem_equation_ck G (Env.map (fun _ => Streams.const absent) (fst H), Env.map (fun _ => Streams.const absent) (snd H))
                                                       (Streams.const false) eq)
             (P_transitions := fun H _ trans def _ => sem_transitions_ck G (Env.map (fun _ => Streams.const absent) (fst H), Env.map (fun _ => Streams.const absent) (snd H))
                                                                      (Streams.const false) trans def (Streams.const absent))
             (P_block := fun H _ bck => sem_block_ck G (Env.map (fun _ => Streams.const absent) (fst H), Env.map (fun _ => Streams.const absent) (snd H))
                                                  (Streams.const false) bck)
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
        + eapply sem_var_absent; eauto.
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
        + rewrite Forall3_map_1, Forall3_map_2, Forall3_map_3. rewrite Forall3_map_2 in H5.
          eapply Forall3_impl_In; [|eauto]; intros.
          eapply case_spec. intros n. left.
          repeat split.
          2:rewrite Forall_map; apply Forall_forall; intros (?&?) Hin.
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
          repeat rewrite map_map in *.
          eapply sem_node_ck_morph; try eapply SemN; eauto.
          rewrite <-concat_map, map_map.
          1,2:eapply map_st_EqSt_Proper; try reflexivity.
          1,2:intros * Eq; symmetry; apply mask_absent.
      - (* Equation *)
        econstructor; eauto with lcsem.
        rewrite <-concat_map. simpl_Forall.
        eapply sem_var_absent; eauto.
      - (* Beq *)
        econstructor; eauto.
      - (* Breset *)
        econstructor. eapply H2; eauto.
        apply bools_of_absent.
        intros k. specialize (H4 k) as (_&Hsem').
        eapply Forall_impl; [|eauto]; intros; simpl in *.
        rewrite maskb_absent.
        eapply sem_block_ck_morph; eauto. 2:reflexivity.
        split; simpl; rewrite mask_hist_absent, mask_hist_absent'; reflexivity.
      - (* Bswitch *)
        econstructor; eauto.
        + inv H2; inv H7.
          constructor; auto.
          eapply SForall_forall; intros. rewrite const_nth. constructor.
        + simpl_Forall. do 2 esplit; eauto.
          2:{ destruct s. eapply sem_scope_absent in H5; eauto.
              eapply sem_scope_ck_morph with (P_blk1:=fun Hi => _); eauto.
              - reflexivity.
              - now rewrite ffilterb_absent.
              - intros; simpl. destruct_conjs; auto.
              - intros; destruct_conjs. simpl_Forall.
                eapply sem_block_ck_morph in H7; eauto. reflexivity.
                now rewrite ffilterb_absent.
          }
          destruct H3 as (Hfilter1&Hfilter2).
          split; simpl in *.
          * eapply filter_hist_absent; eauto.
          * rewrite ffilter_hist_absent, <-ffilter_hist_absent' with (H:=snd Hi).
            eapply Env.map_Equiv; eauto. intros; reflexivity.
      - (* default transition *)
        constructor. apply ntheq_eqst; intros.
        setoid_rewrite Str_nth_map. rewrite 2 const_nth. auto.
      - (* transition *)
        econstructor; eauto using bools_of_absent.
        apply ntheq_eqst; intros.
        rewrite choose_first_nth. setoid_rewrite Str_nth_map. rewrite 2 const_nth; auto.
      - (* Bauto *)
        econstructor; eauto using sem_clock_absent, fby_absent.
        simpl_Forall. specialize (H4 k); destruct_conjs.
        destruct H4 as (Hsel1&Hsel2).
        do 2 esplit; eauto.
        2:{ destruct s. eapply sem_scope_absent in H6; eauto.
            eapply sem_scope_ck_morph with (P_blk1:=fun Hi blks => Forall _ (fst blks) /\ sem_transitions_ck _ _ _ (snd blks) _ _); eauto.
            - reflexivity.
            - now rewrite fselectb_absent.
            - intros; simpl. destruct_conjs; auto.
            - intros; destruct_conjs; split.
              + simpl_Forall.
                eapply sem_block_ck_morph in H7; eauto. reflexivity.
                now rewrite fselectb_absent.
              + now rewrite fselectb_absent, fselect_absent.
        }
        split; simpl in *.
        + eapply select_hist_absent; eauto.
        + rewrite fselect_hist_absent, <-fselect_hist_absent' with (H:=h0).
          eapply Env.map_Equiv; eauto. intros; reflexivity.
      - (* Blocal *)
        econstructor. destruct scope0.
        eapply sem_scope_absent in H0; eauto.
        + intros; destruct_conjs; simpl; auto.
        + intros; simpl in *. destruct_conjs; auto.
      - (* Node *)
        econstructor. 5:reflexivity. 1-4:eauto; subst.
        1,2:(rewrite Forall2_map_2; eapply Forall2_impl_In; [|eauto];
             intros; eapply sem_var_absent; eauto).
        + rewrite clocks_of_false; auto.
        + rewrite clocks_of_false.
          eapply clocked_node_absent in H7; eauto.
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

End LCLOCKSEMANTICS.

Module LClockSemanticsFun
       (Ids : IDS)
       (Op : OPERATORS)
       (OpAux : OPERATORS_AUX Ids Op)
       (Cks : CLOCKS Ids Op OpAux)
       (Senv  : STATICENV Ids Op OpAux Cks)
       (Syn : LSYNTAX Ids Op OpAux Cks Senv)
       (Typ : LTYPING Ids Op OpAux Cks Senv Syn)
       (Clo : LCLOCKING Ids Op OpAux Cks Senv Syn)
       (LCA : LCAUSALITY Ids Op OpAux Cks Senv Syn)
       (Lord : LORDERED Ids Op OpAux Cks Senv Syn)
       (CStr : COINDSTREAMS Ids Op OpAux Cks)
       (Sem : LSEMANTICS Ids Op OpAux Cks Senv Syn Lord CStr)
<: LCLOCKSEMANTICS Ids Op OpAux Cks Senv Syn Typ Clo LCA Lord CStr Sem.
  Include LCLOCKSEMANTICS Ids Op OpAux Cks Senv Syn Typ Clo LCA Lord CStr Sem.
End LClockSemanticsFun.
