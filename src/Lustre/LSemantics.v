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

  Definition history : Type := (history * history).

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

    Definition mask_hist k rs H := (mask_hist k rs (fst H), mask_hist k rs (snd H)).
    Definition filter_hist e cs Hi Hi' :=
      filter_hist e cs (fst Hi) (fst Hi')
      /\ FEnv.Equiv (@EqSt _) (snd Hi') (ffilter_hist e cs (snd Hi)).
    Definition select_hist e k stres Hi Hi' :=
      select_hist e k stres (fst Hi) (fst Hi')
      /\ FEnv.Equiv (@EqSt _) (snd Hi') (fselect_hist e k stres (snd Hi)).

    Section sem_scope.

      Context {A : Type}.

      Variable sem_exp : history -> exp -> list (Stream svalue) -> Prop.
      Variable sem_block : history -> A -> Prop.

      Inductive sem_scope : history -> Stream bool -> (scope A) -> Prop :=
      | Sscope : forall Hi Hi' Hl Hl' bs locs caus blks,
          (* Content of the internal history : bottom-up constraints *)
          (forall x vs, sem_var Hi' x vs -> ~InMembers x locs -> sem_var Hi x vs) ->

          (* Content of the last history : top-down constraints *)
          Hl ⊑ Hl' ->
          (forall x ty ck cx e0 clx,
              In (x, (ty, ck, cx, Some (e0, clx))) locs ->
              exists vs0 vs1 vs,
                sem_exp (Hi', Hl') e0 [vs0]
                /\ sem_var Hi' x vs1
                /\ fby vs0 vs1 vs
                /\ sem_var Hl' x vs) ->

          sem_block (Hi', Hl') blks ->
          sem_scope (Hi, Hl) bs (Scope locs caus blks).
    End sem_scope.

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
        sem_var (fst H) x s ->
        sem_exp H b (Evar x ann) [s]

    | Slast:
      forall H b x s ann,
        sem_var (snd H) x s ->
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
        sem_var (fst H) x s ->
        Forall2 (fun s' => when k s' s) (concat ss) os ->
        sem_exp H b (Ewhen es (x, tx) k lann) os

    | Smerge:
      forall H b x tx s es lann vs os,
        sem_var (fst H) x s ->
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
          Forall2 (sem_var (fst H)) xs (concat ss) ->
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
                  exists Hi', filter_hist (fst blks) sc Hi Hi'
                         /\ let bi := ffilterb (fst blks) sc b in
                           sem_scope (fun Hi' => sem_exp Hi' bi)
                                     (fun Hi' => Forall (sem_block Hi' bi)) Hi' bi (snd blks)) branches ->
        sem_block Hi b (Bswitch ec branches)

    | SautoWeak:
      forall H bs ini oth states ck bs' stres0 stres1 stres,
        sem_clock (fst H) bs ck bs' ->
        sem_transitions H bs' (List.map (fun '(e, t) => (e, (t, false))) ini) (oth, false) stres0 ->
        fby stres0 stres1 stres ->
        Forall (fun state =>
                  let tag := fst (fst state) in
                  forall k, exists Hik, select_hist tag k stres H Hik
                              /\ let bik := fselectb tag k stres bs in
                                sem_scope (fun Hi' => sem_exp Hi' bik)
                                          (fun Hi' blks =>
                                             Forall (sem_block Hi' bik) (fst blks)
                                             /\ sem_transitions Hi' bik (snd blks) (tag, false) (fselect absent tag k stres stres1)
                                          ) Hik bik (snd (snd state))
               ) states ->
        sem_block H bs (Bauto Weak ck (ini, oth) states)

    | SautoStrong:
      forall H bs ini states ck bs' stres stres1,
        sem_clock (fst H) bs ck bs' ->
        fby (const_stres bs' (ini, false)) stres1 stres ->
        Forall (fun state =>
                  let tag := fst (fst state) in
                  forall k, exists Hik, select_hist tag k stres H Hik
                              /\ let bik := fselectb tag k stres bs in
                                sem_transitions Hik bik (fst (snd state)) (tag, false) (fselect absent tag k stres stres1)
               ) states ->
        Forall (fun state =>
                  let tag := fst (fst state) in
                  forall k, exists Hik, select_hist tag k stres1 H Hik
                              /\ let bik := fselectb tag k stres1 bs in
                                sem_scope (fun Hi' => sem_exp Hi' bik)
                                          (fun Hi' blks => Forall (sem_block Hi' bik) (fst blks)
                                          ) Hik bik (snd (snd state))
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
          Forall2 (sem_var H) (idents n.(n_in)) ss ->
          Forall2 (sem_var H) (idents n.(n_out)) os ->
          sem_block (H, FEnv.empty _) b n.(n_block) ->
          b = clocks_of ss ->
          sem_node f ss os.

  End NodeSemantics.

  (** Custom induction schemes *)

  Section sem_exp_ind2.
    Context (PSyn : block -> Prop).
    Context (prefs : PS.t).
    Variable G : @global PSyn prefs.

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
        sem_var (fst H) x s ->
        P_exp H b (Evar x ann) [s].

    Hypothesis LastCase:
      forall H b x s ann,
        sem_var (snd H) x s ->
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
        sem_var (fst H) x s ->
        Forall2 (fun s' => when k s' s) (concat ss) os ->
        P_exp H b (Ewhen es (x, tx) k lann) os.

    Hypothesis MergeCase:
      forall H b x tx s es lann vs os,
        sem_var (fst H) x s ->
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
        Forall2 (sem_var (fst H)) xs (concat ss) ->
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
        Forall (fun blks => exists Hi', filter_hist (fst blks) sc Hi Hi'
                                /\ let bi := ffilterb (fst blks) sc b in
                                  sem_scope (fun Hi' e vs => sem_exp G Hi' bi e vs /\ P_exp Hi' bi e vs)
                                            (fun Hi' blks => Forall (sem_block G Hi' bi) blks
                                                          /\ Forall (P_block Hi' bi) blks
                                            ) Hi' bi (snd blks)) branches ->
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
        sem_clock (fst Hi) bs ck bs' ->
        sem_transitions G Hi bs' (List.map (fun '(e, t) => (e, (t, false))) ini) (oth, false) stres0 ->
        P_transitions Hi bs' (List.map (fun '(e, t) => (e, (t, false))) ini) (oth, false) stres0 ->
        fby stres0 stres1 stres ->
        Forall (fun '((tag, _), (_, scope)) =>
                  forall k, exists Hik,
                    select_hist tag k stres Hi Hik
                    /\ let bik := fselectb tag k stres bs in
                      sem_scope (fun Hi' e vs => sem_exp G Hi' bik e vs /\ P_exp Hi' bik e vs)
                                (fun Hi' blks => Forall (sem_block G Hi' bik) (fst blks)
                                              /\ Forall (P_block Hi' bik) (fst blks)
                                              /\ sem_transitions G Hi' bik (snd blks) (tag, false) (fselect absent tag k stres stres1)
                                              /\ P_transitions Hi' bik (snd blks) (tag, false) (fselect absent tag k stres stres1)
                                ) Hik bik scope
               ) states ->
        P_block Hi bs (Bauto Weak ck (ini, oth) states).

    Hypothesis BautoStrongCase:
      forall Hi bs ini states ck bs' stres0 stres1,
        sem_clock (fst Hi) bs ck bs' ->
        fby (const_stres bs' (ini, false)) stres1 stres0 ->
        Forall (fun '((tag, _), (unl, _)) =>
                  forall k, exists Hik, select_hist tag k stres0 Hi Hik
                              /\ let bik := fselectb tag k stres0 bs in
                                sem_transitions G Hik bik unl (tag, false) (fselect absent tag k stres0 stres1)
                                /\ P_transitions Hik bik unl (tag, false) (fselect absent tag k stres0 stres1)
               ) states ->
        Forall (fun '((tag, _), (_, scope)) =>
                  forall k, exists Hik,
                    select_hist tag k stres1 Hi Hik
                    /\ let bik := fselectb tag k stres1 bs in
                      sem_scope (fun Hi' e vs => sem_exp G Hi' bik e vs /\ P_exp Hi' bik e vs)
                                (fun Hi' blks => Forall (sem_block G Hi' bik) (fst blks)
                                              /\ Forall (P_block Hi' bik) (fst blks)
                                ) Hik bik scope
               ) states ->
        P_block Hi bs (Bauto Strong ck ([], ini) states).

    Hypothesis BlocalCase:
      forall Hi bs scope,
        sem_scope (fun Hi' e vs => sem_exp G Hi' bs e vs /\ P_exp Hi' bs e vs)
                  (fun Hi' blks => Forall (sem_block G Hi' bs) blks /\ Forall (P_block Hi' bs) blks)
                  Hi bs scope ->
        P_block Hi bs (Blocal scope).

    Hypothesis Node:
      forall f ss os n H b,
        find_node f G = Some n ->
        Forall2 (sem_var H) (idents n.(n_in)) ss ->
        Forall2 (sem_var H) (idents n.(n_out)) os ->
        sem_block G (H, FEnv.empty _) b n.(n_block) ->
        P_block (H, FEnv.empty _) b n.(n_block) ->
        b = clocks_of ss ->
        P_node f ss os.

    Local Ltac SolveForall :=
      match goal with
      | H: Forall ?P1 ?l |- Forall ?P2 ?l =>
        induction H; auto
      | H: Forall2 ?P1 ?l1 ?l2 |- Forall2 ?P2 ?l1 ?l2 =>
        induction H; auto
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
    with sem_block_ind2
           (H: history) (b: Stream bool) (d: block)
           (Sem: sem_block G H b d)
           {struct Sem}
      : P_block H b d
    with sem_transitions_ind2
           (H: history) (b: Stream bool) trans default stres
           (Sem: sem_transitions G H b trans default stres)
           {struct Sem}
         : P_transitions H b trans default stres
    with sem_node_ind2
           (f: ident) (ss os: list (Stream svalue))
           (Sem: sem_node G f ss os)
           {struct Sem}
         : P_node f ss os.
    Proof.
      - destruct Sem.
        + apply ConstCase; eauto.
        + apply EnumCase; eauto.
        + apply VarCase; auto.
        + apply LastCase; auto.
        + eapply UnopCase; eauto.
        + eapply BinopCase; eauto.
        + eapply FbyCase; eauto; clear H2; SolveForall.
        + eapply ArrowCase; eauto; clear H2; SolveForall.
        + eapply WhenCase; eauto; clear H2; SolveForall.
        + eapply MergeCase; eauto; clear H2; SolveForall.
          induction H1; econstructor; eauto. clear IHForall2Brs H3. SolveForall.
        + eapply CaseTotalCase; eauto; clear H1.
          induction H0; econstructor; eauto. clear IHForall2Brs H2. SolveForall.
        + eapply CaseDefaultCase; eauto.
          * clear - sem_exp_ind2 H1.
            induction H1; econstructor; eauto. clear IHForall2Brs H2. SolveForall.
          * clear - sem_exp_ind2 H2.
            SolveForall.
        + eapply AppCase; eauto; clear H2 H3; SolveForall.
      - destruct Sem.
        eapply Equation with (ss:=ss); eauto; clear H1; SolveForall.
      - destruct Sem.
        + apply BeqCase; eauto.
        + eapply BresetCase; eauto.
          intros k. specialize (H2 k). split; eauto. SolveForall.
        + eapply BswitchCase; eauto.
          SolveForall. constructor; auto.
          destruct_conjs.
          inv H3. destruct_conjs. do 2 esplit; eauto.
          destruct Hi. econstructor; eauto. 2:split; eauto.
          * intros * Hin. eapply H8 in Hin as (?&?&?&?&?&?&?). do 3 esplit; eauto.
            repeat split; eauto.
          * simpl. SolveForall.
        + eapply BautoWeakCase; eauto.
          SolveForall; destruct_conjs. constructor; auto.
          intros k. specialize (H3 k). destruct_conjs.
          take (sem_scope _ _ _ _ _) and inv it. destruct_conjs.
          esplit. split; eauto.
          econstructor; eauto. 2:split; [|split; [|split]]; eauto.
          * intros * Hin. eapply H8 in Hin as (?&?&?&?&?&?&?). do 3 esplit; eauto.
            repeat split; eauto.
          * simpl. SolveForall.
        + eapply BautoStrongCase; eauto.
          * clear - H2 sem_transitions_ind2. SolveForall. destruct_conjs. constructor; auto.
            intros k. specialize (H0 k). destruct_conjs. eauto.
          * clear H2. SolveForall. destruct_conjs. constructor; auto.
            intros k. specialize (H2 k). destruct_conjs.
            take (sem_scope _ _ _ _ _) and inv it. destruct_conjs.
            do 2 esplit; eauto. econstructor; eauto.
            2:split; auto; simpl.
            -- intros * Hin. eapply H7 in Hin as (?&?&?&?&?&?&?). do 3 esplit; eauto.
               repeat split; eauto.
            -- SolveForall.
        + eapply BlocalCase; eauto.
          inv H. econstructor; eauto.
          2:split; auto; SolveForall.
          intros * Hin.
          eapply H2 in Hin as (?&?&?&?&?&?&?). do 3 esplit; eauto.
          repeat split; eauto.
      - destruct Sem.
        + eapply TransDefCase; eauto.
        + eapply TransCase; eauto.
      - destruct Sem.
        eapply Node; eauto.
    Qed.

  End sem_exp_ind2.

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

  Ltac sem_block_cons :=
    intros; simpl_Forall; solve_Exists;
    match goal with
    | H: Forall2Brs _ ?l1 ?l2 |- Forall2Brs _ ?l1 ?l2 =>
        eapply Forall2Brs_impl_In in H; eauto; intros; sem_block_cons
    | H: _ -> ?G |- ?G => eapply H; sem_block_cons
    | Hname: n_name ?nd <> _, Hfind: find_node _ {| types := _; nodes := ?nd :: _ |} = _ |- _ =>
        rewrite find_node_other in Hfind; auto
    | Hname: n_name ?nd <> _ |- find_node _ {| types := _; nodes := ?nd :: _ |} = _ =>
        rewrite find_node_other; auto
    | Hname: n_name ?nd <> _ |- ~_ => idtac
    | H: ~Is_node_in_exp _ (Eapp _ _ _ _) |- _ <> _ => contradict H; subst; eapply INEapp2
    | H: ~_ |- ~_ => contradict H; try constructor; unfold Is_node_in_eq in *; sem_block_cons
    | |- _ \/ _ => solve [left;sem_block_cons|right;sem_block_cons]
    | |- exists d, Some _ = Some d /\ List.Exists _ d =>
        do 2 esplit; [reflexivity|sem_block_cons]
    | k: nat,H: forall (_ : nat), _ |- _ => specialize (H k); sem_block_cons
    | H: Forall2 _ ?xs _ |- Forall2 _ ?xs _ =>
        eapply Forall2_impl_In in H; eauto; intros; sem_block_cons
    | |- exists _, filter_hist _ _ _ _ /\ _ =>
        do 2 esplit; [auto|sem_block_cons]
    | |- exists _, select_hist _ _ _ _ _ /\ _ =>
        do 2 esplit; [auto|sem_block_cons]
    | H: forall _ _ _ _ _ _, In _ _ -> exists _ _ _, _ /\ _ /\ _ /\ _ |- exists _ _ _, _ /\ _ /\ _ /\ _ =>
        edestruct H as (?&?&?&?&?&?&?); eauto;
        do 3 esplit; split; [|split; [|split]]; eauto; sem_block_cons
    | H:sem_scope _ _ _ _ _ |- sem_scope _ _ _ _ _ =>
        inv H; destruct_conjs; econstructor; eauto
    | |- Is_node_in_scope _ _ _ => econstructor; sem_block_cons
    | |- _ /\ _ => split; sem_block_cons
    | |- exists _ _, _ /\ _ /\ _ =>
        do 2 esplit; split; [|split]; eauto; sem_block_cons
    | _ => auto
    end.

  Lemma sem_block_cons {PSyn prefs} :
    forall (nd : @node PSyn prefs) nds types bck H bk,
      Ordered_nodes (Global types (nd::nds))
      -> sem_block (Global types (nd::nds)) H bk bck
      -> ~Is_node_in_block nd.(n_name) bck
      -> sem_block (Global types nds) H bk bck.
  Proof.
    intros * Hord Hsem Hnf.
    revert Hnf.
    induction Hsem using sem_block_ind2
      with
        (P_block := fun bk H d => ~Is_node_in_block nd.(n_name) d
                                     -> sem_block (Global types0 nds) bk H d)
        (P_transitions := fun bk H trans default stres => ~List.Exists (fun '(e, _) => Is_node_in_exp nd.(n_name) e) trans
                                                       -> sem_transitions (Global types0 nds) bk H trans default stres)
        (P_equation := fun bk H eq => ~Is_node_in_eq nd.(n_name) eq
                                   -> sem_equation (Global types0 nds) bk H eq)
        (P_exp := fun H bk e ss => ~ Is_node_in_exp nd.(n_name) e
                                -> sem_exp (Global types0 nds) H bk e ss)
        (P_node := fun f xs ys => nd.(n_name) <> f -> sem_node (Global types0 nds) f xs ys);
      try (now econstructor; eauto); intros.

    all:econstructor; eauto; repeat sem_block_cons.
    - eapply find_node_later_not_Is_node_in; eauto.
  Qed.

  Corollary sem_node_cons {PSyn prefs} :
    forall (nd : @node PSyn prefs) nds types f xs ys,
      Ordered_nodes (Global types (nd::nds))
      -> sem_node (Global types (nd::nds)) f xs ys
      -> nd.(n_name) <> f
      -> sem_node (Global types nds) f xs ys.
  Proof.
    intros * Hord Hsem Hnf.
    inv Hsem.
    rewrite find_node_other with (1:=Hnf) in H0.
    econstructor; eauto.
    eapply sem_block_cons; eauto.
    eapply find_node_later_not_Is_node_in; eauto.
  Qed.

  Lemma sem_block_cons' {PSyn prefs} :
    forall (nd : @node PSyn prefs) nds types bck H bk,
      Ordered_nodes (Global types (nd::nds))
      -> sem_block (Global types nds) H bk bck
      -> ~Is_node_in_block nd.(n_name) bck
      -> sem_block (Global types (nd::nds)) H bk bck.
  Proof.
    intros * Hord Hsem Hnf.
    revert Hnf.
    induction Hsem using sem_block_ind2
      with
        (P_block := fun bk H d => ~Is_node_in_block nd.(n_name) d
                               -> sem_block (Global types0 (nd::nds)) bk H d)
        (P_transitions := fun bk H trans default stres => ~List.Exists (fun '(e, _) => Is_node_in_exp nd.(n_name) e) trans
                                                       -> sem_transitions (Global types0 (nd::nds)) bk H trans default stres)
        (P_equation := fun bk H eq => ~Is_node_in_eq nd.(n_name) eq
                                   -> sem_equation (Global types0 (nd::nds)) bk H eq)
        (P_exp := fun H bk e ss => ~ Is_node_in_exp nd.(n_name) e
                                -> sem_exp (Global types0 (nd::nds)) H bk e ss)
        (P_node := fun f xs ys => nd.(n_name) <> f -> sem_node (Global types0 (nd::nds)) f xs ys);
      try (now econstructor; eauto); intros.
    all:econstructor; eauto; repeat sem_block_cons.
    - eapply find_node_later_not_Is_node_in; eauto.
  Qed.

  Corollary sem_node_cons' {PSyn prefs} :
    forall (nd : @node PSyn prefs) nds types f xs ys,
      Ordered_nodes (Global types (nd::nds))
      -> sem_node (Global types nds) f xs ys
      -> nd.(n_name) <> f
      -> sem_node (Global types (nd::nds)) f xs ys.
  Proof.
    intros * Hord Hsem Hneq.
    inv Hsem.
    econstructor; eauto.
    erewrite <-find_node_other in H0; eauto.
    eapply sem_block_cons'; eauto.
    eapply find_node_later_not_Is_node_in in H0; eauto.
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

  Add Parametric Morphism op t : (lift1 op t)
      with signature @EqSt svalue ==> @EqSt svalue ==> Basics.impl
        as lift1_EqSt.
  Proof.
    cofix Cofix.
    intros es es' Ees ys ys' Eys Lift.
    destruct es' as [[]], ys' as [[]];
      inv Lift; inv Eys; inv Ees; simpl in *; try discriminate.
    - constructor; eapply Cofix; eauto.
    - constructor.
      + now inv H1; inv H3.
      + eapply Cofix; eauto.
  Qed.

  Add Parametric Morphism op t1 t2 : (lift2 op t1 t2)
      with signature @EqSt svalue ==> @EqSt svalue ==> @EqSt svalue ==> Basics.impl
        as lift2_EqSt.
  Proof.
    cofix Cofix.
    intros e1s e1s' Ee1s e2s e2s' Ee2s ys ys' Eys Lift.
    destruct e1s' as [[]], e2s' as [[]], ys' as [[]];
      inv Lift; inv Eys; inv Ee1s; inv Ee2s; simpl in *; try discriminate.
    - constructor; eapply Cofix; eauto.
    - constructor.
      + now inv H1; inv H3; inv H5.
      + eapply Cofix; eauto.
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

  Add Parametric Morphism : sem_var
      with signature FEnv.Equiv (@EqSt _) ==> eq ==> @EqSt svalue ==> Basics.impl
        as sem_var_EqSt.
  Proof.
    intros H H' EH x xs xs' E; intro Sem; inv Sem.
    specialize (EH x). rewrite H1 in EH. inv EH.
    econstructor; eauto.
    now rewrite <-E, H2, H4.
  Qed.

  Definition history_equiv (Hi1 Hi2 : history) : Prop :=
    FEnv.Equiv (@EqSt _) (fst Hi1) (fst Hi2) /\ FEnv.Equiv (@EqSt _) (snd Hi1) (snd Hi2).

  Global Instance history_equiv_refl : Reflexive history_equiv.
  Proof. split; reflexivity. Qed.

  Add Parametric Morphism {PSyn prefs} (G : @global PSyn prefs) : (sem_exp G)
      with signature history_equiv ==> @EqSt bool ==> eq ==> @EqSts svalue ==> Basics.impl
        as sem_exp_morph.
  Proof.
    intros H H' EH b b' Eb e xs xs' Exs Sem.
    revert H' b' xs' EH Eb Exs; induction Sem using sem_exp_ind2 with
                                    (P_equation := fun H b e => True)
                                    (P_transitions := fun _ _ _ _ _ => True)
                                    (P_block := fun H b d => True)
                                    (P_node := fun i xs ys => forall ys', EqSts ys ys' -> sem_node G i xs ys');
      auto; intros;
      unfold EqSts in *; simpl_Forall.
    - econstructor; rewrite <-Eb; etransitivity; eauto; now symmetry.
    - econstructor; rewrite <-Eb; etransitivity; eauto; now symmetry.
    - constructor. destruct EH as (EH&_). now rewrite <-EH, <-H3.
    - constructor. destruct EH as (_&EH). now rewrite <-EH, <-H3.
    - econstructor; eauto.
      + apply IHSem; eauto; reflexivity.
      + now rewrite <-H4.
    - econstructor; eauto.
      + apply IHSem1; eauto; reflexivity.
      + apply IHSem2; eauto; reflexivity.
      + now rewrite <-H5.
    - econstructor.
      + eapply Forall2_impl_In; [|apply H1].
        intros * ?? Hs; apply Hs; auto; reflexivity.
      + eapply Forall2_impl_In; [|apply H3].
        intros * ?? Hs; apply Hs; auto; reflexivity.
      + eapply Forall3_EqSt; eauto. solve_proper.
    - econstructor.
      + eapply Forall2_impl_In; [|apply H1].
        intros * ?? Hs; apply Hs; auto; reflexivity.
      + eapply Forall2_impl_In; [|apply H3].
        intros * ?? Hs; apply Hs; auto; reflexivity.
      + eapply Forall3_EqSt; eauto. solve_proper.
    - econstructor; eauto.
      + eapply Forall2_impl_In; [|apply H1].
        intros * ?? Hs; apply Hs; auto; reflexivity.
      + destruct EH as (EH&_). rewrite <-EH; eauto.
      + eapply Forall2_EqSt; eauto. solve_proper.
    - econstructor; eauto.
      + destruct EH as (EH&_). rewrite <-EH; eauto.
      + instantiate (1:=vs).
        eapply Forall2Brs_impl_In; [|eapply H2]; intros ?? _ Hs.
        eapply Hs; eauto. reflexivity.
      + rewrite <-Exs; auto.
    - econstructor; eauto.
      + eapply IHSem; eauto. reflexivity.
      + instantiate (1:=vs).
        eapply Forall2Brs_impl_In; [|eapply H1]; intros ?? _ Hs.
        eapply Hs; eauto. reflexivity.
      + eapply Forall3_EqSt_Proper; eauto. solve_proper.
    - econstructor; eauto.
      + eapply IHSem; eauto. reflexivity.
      + instantiate (1:=vs).
        eapply Forall2Brs_impl_In; [|eapply H2]; intros ?? _ Hs.
        eapply Hs; eauto. reflexivity.
      + instantiate (1:=vd).
        eapply Forall2_impl_In; [|apply H4]; intros ?? _ _ Hs.
        eapply Hs; eauto. reflexivity.
      + eapply Forall3_EqSt_Proper; eauto. solve_proper.
    - econstructor; eauto.
      + eapply Forall2_impl_In; [|apply H1].
        intros * ?? Hs; apply Hs; auto; reflexivity.
      + eapply Forall2_impl_In; [|apply H3].
        intros * ?? Hs; apply Hs; auto; reflexivity.
      + intro k; specialize (H5 k); destruct H5 as (?&Hr).
        apply Hr.
        apply map_st_EqSt_Proper; auto.
        intros ?? ->; reflexivity.

    - econstructor; eauto.
      eapply Forall2_EqSt; eauto. solve_proper.
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
      destruct EH as (EH&_). now rewrite <-EH.
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

  Add Parametric Morphism {PSyn prefs} (G : @global PSyn prefs) : (sem_block G)
      with signature history_equiv ==> @EqSt bool ==> eq ==> Basics.impl
        as sem_block_morph.
  Proof.
    unfold Basics.impl; intros H H' EH b b' Eb d Sem.
    revert H' b' EH Eb; induction Sem using sem_block_ind2
      with (P_exp := fun _ _ _ _ => True)
           (P_transitions := fun _ _ _ _ _ => True)
           (P_equation := fun _ _ _ => True)
           (P_node := fun _ _ _ => True); intros; auto.
    - constructor. now rewrite <-EH, <-Eb.
    - econstructor; eauto.
      + now rewrite <-EH, <-Eb.
      + intros k. specialize (H2 k) as (Hsem&Hsem').
        eapply Forall_Forall in Hsem; eauto. clear Hsem'.
        eapply Forall_impl; [|eauto].
        intros ? (?&?). eapply H2; eauto.
        * destruct EH as (EH1&EH2); split; unfold mask_hist. now rewrite <-EH1. now rewrite <-EH2.
        * now rewrite <-Eb.
    - econstructor; eauto.
      + now rewrite <-EH, <-Eb.
      + simpl_Forall. inv H3.
        do 2 esplit. 2:econstructor; eauto.
        * destruct EH as (EH1&EH2); unfold filter_hist in *.
          destruct H1. split. rewrite <-EH1 at 1. eauto. rewrite <-EH2 at 1. eauto.
        * intros * Hin. edestruct H8 as (?&?&?&(?&_)&?&?&?); eauto.
          do 3 esplit. repeat (split; eauto).
          now rewrite <-Eb.
        * simpl_Forall. eapply H5; eauto. reflexivity. now rewrite <-Eb.
    - econstructor; eauto.
      + destruct EH as (EH1&EH2). rewrite <-EH1, <-Eb; eauto.
      + now rewrite <-EH.
      + simpl_Forall. specialize (H2 k) as ((Hik&Hikl)&?). destruct_conjs.
        inv H4; destruct_conjs.
        exists (Hik, Hikl). split; [|econstructor; repeat split]; eauto.
        * destruct EH as (EH1&EH2). destruct H2 as (Hsel1&Hsel2).
          split. rewrite <-EH1; auto. rewrite <-EH2; auto.
        * intros * Hin. edestruct H9 as (?&?&?&(?&_)&?&?&?); eauto.
          do 3 esplit. repeat (split; eauto).
          now rewrite <-Eb.
        * simpl_Forall. eapply H5; eauto. reflexivity. now rewrite <-Eb.
        * now rewrite <-Eb.
    - econstructor; eauto.
      + destruct EH as (EH1&EH2). rewrite <-EH1, <-Eb; eauto.
      + simpl_Forall. specialize (H1 k) as ((Hik&Hikl)&?). destruct_conjs.
        exists (Hik, Hikl). split.
        * destruct EH as (EH1&EH2). destruct H1 as (Hsel1&Hsel2).
          split. rewrite <-EH1; auto. rewrite <-EH2; auto.
        * now rewrite <-Eb.
      + simpl_Forall. specialize (H2 k) as ((Hik&Hikl)&?). destruct_conjs.
        inv H4; destruct_conjs.
        exists (Hik, Hikl). split; [|econstructor; repeat split]; eauto.
        * destruct EH as (EH1&EH2). destruct H2 as (Hsel1&Hsel2).
          split. rewrite <-EH1; auto. rewrite <-EH2; auto.
        * intros * Hin. edestruct H9 as (?&?&?&(?&_)&?&?&?); eauto.
          do 3 esplit. repeat (split; eauto).
          now rewrite <-Eb.
        * simpl_Forall. eapply H5; eauto. reflexivity. now rewrite <-Eb.

    - constructor. destruct EH as (EH1&EH2).
      inv H; destruct_conjs. destruct H'. eapply Sscope with (Hi':=Hi') (Hl':=Hl').
      + now setoid_rewrite <-EH1.
      + now rewrite <-EH2.
      + intros. edestruct H2; eauto. destruct_conjs.
        do 3 esplit; eauto. repeat split; eauto.
        now rewrite <-Eb.
      + simpl_Forall.
        eapply H3; eauto. reflexivity.
  Qed.

  Add Parametric Morphism {PSyn prefs} (G : @global PSyn prefs) : (sem_node G)
      with signature eq ==> @EqSts svalue ==> @EqSts svalue ==> Basics.impl
        as sem_node_morph.
  Proof.
    unfold Basics.impl; intros f xss xss' Exss yss yss' Eyss Sem.
    induction Sem.
    subst.
    econstructor; try reflexivity; eauto.
    + instantiate (1 := H). now rewrite <-Exss.
    + now rewrite <-Eyss.
    + now rewrite <-Exss.
  Qed.

  Fact sem_var_In : forall H x vs,
      sem_var H x vs ->
      FEnv.In x H.
  Proof.
    intros * Hv. inv Hv.
    econstructor; eauto.
  Qed.

  Corollary sem_vars_In : forall H xs vs,
      Forall2 (sem_var H) xs vs ->
      Forall (fun v => FEnv.In v H) xs.
  Proof.
    intros * Hvs.
    induction Hvs; constructor; eauto using sem_var_In.
  Qed.

  (** ** All the defined variables have a semantic *)

  Lemma sem_block_defined {PSyn prefs} (G: @global PSyn prefs) : forall blk H bs x,
      sem_block G H bs blk ->
      Is_defined_in x blk ->
      FEnv.In x (fst H).
  Proof.
    induction blk using block_ind2; intros * Hsem Hdef; inv Hsem; inv Hdef.
    - (* equation *)
      inv H4. eapply Forall2_ignore2, Forall_forall in H8 as (?&?&?); eauto using sem_var_In.
    - (* reset *)
      specialize (H8 0).
      simpl_Exists; simpl_Forall.
      destruct H0; simpl in *. eapply H in H8; eauto.
      setoid_rewrite FEnv.map_in_iff in H8; eauto.
    - (* switch *)
      simpl_Exists; simpl_Forall.
      destruct s; inv H2; inv H4.
      simpl_Exists. simpl_Forall.
      eapply H in H16; eauto. inv H16.
      destruct H1. eapply FEnv.In_refines; eauto.
      eapply sem_var_In, H13; eauto.
      econstructor; eauto. reflexivity.
    - (* automaton *)
      simpl_Exists; simpl_Forall. specialize (H11 0); destruct_conjs.
      destruct s; destruct_conjs. inv H3; inv H2.
      simpl_Exists. simpl_Forall.
      eapply H in H2; eauto. inv H2.
      destruct H1. eapply FEnv.In_refines; eauto.
      eapply sem_var_In, H13; eauto.
      econstructor; eauto. reflexivity.
    - (* automaton *)
      simpl_Exists; simpl_Forall. specialize (H11 0); destruct_conjs.
      destruct s; destruct_conjs. inv H3; inv H2.
      simpl_Exists. simpl_Forall.
      eapply H in H16; eauto. inv H16.
      destruct H1. eapply FEnv.In_refines; eauto.
      eapply sem_var_In, H13; eauto.
      econstructor; eauto. reflexivity.
    - (* local *)
      inv H4. inv H2. simpl_Exists; simpl_Forall.
      eapply H in H11; eauto. inv H11.
      eapply sem_var_In, H6; eauto.
      econstructor; eauto. reflexivity.
  Qed.

  Corollary Forall_sem_block_defined {PSyn prefs} (G: @global PSyn prefs) : forall blks x H bs,
      Forall (sem_block G H bs) blks ->
      List.Exists (Is_defined_in x) blks ->
      FEnv.In x (fst H).
  Proof.
    intros * Hsem Hdef; simpl_Exists; simpl_Forall.
    eapply sem_block_defined; eauto.
  Qed.

  Lemma sem_scope_defined {PSyn prefs} (G: @global PSyn prefs) : forall locs caus blks Hi bs x,
      sem_scope (fun Hi => sem_exp G Hi bs) (fun Hi => Forall (sem_block G Hi bs)) Hi bs (Scope locs caus blks) ->
      Is_defined_in_scope (List.Exists (Is_defined_in x)) x (Scope locs caus blks) ->
      FEnv.In x (fst Hi).
  Proof.
    intros * Hsem Hdef; inv Hsem; inv Hdef.
    eapply Forall_sem_block_defined in H7; eauto. inv H7.
    eapply sem_var_In, H2; eauto.
    econstructor; eauto. reflexivity.
  Qed.

  Corollary sem_scope_defined1 {PSyn prefs} (G: @global PSyn prefs) :
    forall locs caus blks Hi bs Γ xs x,
      sem_scope (fun Hi => sem_exp G Hi bs) (fun Hi => Forall (sem_block G Hi bs)) Hi bs (Scope locs caus blks) ->
      VarsDefinedScope (fun blks ys => exists xs, Forall2 VarsDefined blks xs /\ Permutation (concat xs) ys) (Scope locs caus blks) xs ->
      NoDupScope (fun Γ => Forall (NoDupLocals Γ)) Γ (Scope locs caus blks) ->
      incl xs Γ ->
      In x xs ->
      FEnv.In x (fst Hi).
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
    forall locs caus (blks: _ * A) Hi bs Γ xs x,
      sem_scope (fun Hi => sem_exp G Hi bs) (fun Hi blks => Forall (sem_block G Hi bs) (fst blks)) Hi bs (Scope locs caus blks) ->
      VarsDefinedScope (fun blks ys => exists xs, Forall2 VarsDefined (fst blks) xs /\ Permutation (concat xs) ys) (Scope locs caus blks) xs ->
      NoDupScope (fun Γ blks => Forall (NoDupLocals Γ) (fst blks)) Γ (Scope locs caus blks) ->
      incl xs Γ ->
      In x xs ->
      FEnv.In x (fst Hi).
  Proof.
    intros * Hsem Hdef Hnd Hincl Hinxs.
    eapply sem_scope_defined1 with (caus:=caus); eauto.
    - inv Hsem; econstructor; eauto.
    - inv Hdef; econstructor; eauto.
    - inv Hnd; econstructor; eauto.
  Qed.

  (** ** Preservation of the semantics while refining an environment *)
  (** If a new environment [refines] the previous one, it gives the same semantics
      to variables and therefore expressions, equations dans nodes *)

  Fact refines_eq_EqSt {A} : forall H H' ,
      FEnv.refines eq H H' ->
      FEnv.refines (@EqSt A) H H'.
  Proof.
    intros * Href ?? Hfind.
    eapply Href in Hfind as (?&?&Hfind); subst.
    rewrite Hfind. do 2 esplit; eauto.
    reflexivity.
  Qed.

  Fact sem_var_refines : forall H H' id v,
      H ⊑ H' ->
      sem_var H id v ->
      sem_var H' id v.
  Proof.
    intros H H' id v Href Hsem.
    destruct Hsem. eapply Href in H0 as (?&?&Hfind).
    econstructor; eauto.
    etransitivity; eauto.
  Qed.

  Lemma sem_var_refines_inv : forall env Hi1 Hi2 x vs,
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

  Lemma sem_var_refines' : forall Hi1 Hi2 x vs,
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

  Corollary sem_var_refines'' : forall env Hi1 Hi2 x vs,
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

  Fact sem_exp_refines {PSyn prefs} : forall (G : @global PSyn prefs) b e H H' Hl v,
      H ⊑ H' ->
      sem_exp G (H, Hl) b e v ->
      sem_exp G (H', Hl) b e v.
  Proof with eauto with datatypes.
    induction e using exp_ind2; intros * Href Hsem; inv Hsem;
      econstructor; eauto using sem_var_refines; simpl_Forall; eauto.
    1-3:(eapply Forall2Brs_impl_In; [|eauto]; intros;
         simpl_Exists; simpl_Forall; eauto).
  Qed.

  Fact sem_equation_refines {PSyn prefs} : forall (G : @global PSyn prefs) H H' Hl b equ,
      H ⊑ H' ->
      sem_equation G (H, Hl) b equ ->
      sem_equation G (H', Hl) b equ.
  Proof with eauto.
    intros * Href Hsem. inv Hsem; simpl in *.
    apply Seq with (ss:=ss); simpl_Forall;
      eauto using sem_exp_refines, sem_var_refines.
  Qed.

  Fact sem_transitions_refines {PSyn prefs} : forall (G : @global PSyn prefs) H H' Hl b trans default stres,
      H ⊑ H' ->
      sem_transitions G (H, Hl) b trans default stres ->
      sem_transitions G (H', Hl) b trans default stres.
  Proof with eauto.
    induction trans; intros * Href Hsem; inv Hsem;
      econstructor; eauto using sem_exp_refines.
  Qed.

  Fact sem_block_refines {PSyn prefs} : forall (G: @global PSyn prefs) d H H' Hl b,
      H ⊑ H' ->
      sem_block G (H, Hl) b d ->
      sem_block G (H', Hl) b d.
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
        destruct H2 as (Href1&?); split; simpl in *; [|auto].
        intros ?? Hfind. apply Href1 in Hfind as (?&Hfilter&Hfind').
        apply Href in Hfind' as (?&?&?). do 2 esplit; [|eauto].
        now rewrite <-H5.
    - (* automaton (weak transitions) *)
      eapply SautoWeak; eauto using sem_clock_refines, sem_transitions_refines.
      simpl_Forall. specialize (H11 k); destruct_conjs.
      destruct s; destruct_conjs. inv H3; destruct_conjs.
      esplit; split; eauto. 2:econstructor; repeat (split; eauto); eauto.
      destruct H2 as (Href1&?); split; simpl in *; [|auto].
      intros ?? Hfind. apply Href1 in Hfind as (?&Hfilter&Hfind').
      apply Href in Hfind' as (?&?&?). do 2 esplit; [|eauto].
      now rewrite <-H5.
    - (* automaton (weak transitions) *)
      eapply SautoStrong; eauto using sem_clock_refines, sem_transitions_refines.
      + simpl_Forall. specialize (H10 k); destruct_conjs.
        esplit; split; eauto.
        destruct H2 as (Href1&?); split; simpl in *; [|auto].
        intros ?? Hfind. apply Href1 in Hfind as (?&Hfilter&Hfind').
        apply Href in Hfind' as (?&?&?). do 2 esplit; [|eauto].
        now rewrite <-H4.
      + simpl_Forall. specialize (H11 k); destruct_conjs.
        destruct s; destruct_conjs. inv H3; destruct_conjs.
        esplit; split; eauto. 2:econstructor; repeat (split; eauto); eauto.
        destruct H2 as (Href1&?); split; simpl in *; [|auto].
        intros ?? Hfind. apply Href1 in Hfind as (?&Hfilter&Hfind').
        apply Href in Hfind' as (?&?&?). do 2 esplit; [|eauto].
        now rewrite <-H3.
    - (* locals *)
      constructor.
      inv H4. econstructor; [| | |eauto]. 1-3:eauto.
      intros ?? Hv Hnin. eapply sem_var_refines; eauto.
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

    Lemma sem_vars_mask_inv: forall k r H xs vs,
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
        exists vs, sem_var (fst Hi) x vs.
    Proof.
      intros * Hdef Hsem.
      eapply sem_block_defined in Hsem as (?&?); eauto.
      do 2 esplit; eauto. reflexivity.
    Qed.

    Corollary sem_block_dom_lb : forall blk xs Hi Hl bs,
        VarsDefined blk xs ->
        NoDupLocals xs blk ->
        sem_block G (Hi, Hl) bs blk ->
        FEnv.dom_lb Hi xs.
    Proof.
      intros * Hvars Hnd Hsem ? Hin.
      eapply VarsDefined_Is_defined in Hin; eauto.
      eapply sem_block_sem_var in Hin as (?&Hvar); eauto.
      simpl in *; eauto using sem_var_In.
    Qed.

    Corollary Forall_sem_block_dom_lb : forall blks xs ys Hi Hl bs,
        Forall2 VarsDefined blks xs ->
        Forall (NoDupLocals ys) blks ->
        Forall (sem_block G (Hi, Hl) bs) blks ->
        Permutation (concat xs) ys ->
        FEnv.dom_lb Hi ys.
    Proof.
      intros * Hvars Hnd Hsem Hperm ? Hin.
      rewrite <-Hperm in Hin.
      eapply Forall_VarsDefined_Is_defined in Hin; eauto.
      2:{ simpl_Forall. eapply NoDupLocals_incl; [|eauto]. now rewrite Hperm. }
      simpl_Exists; simpl_Forall.
      eapply sem_block_sem_var in Hin as (?&Hvar); eauto.
      simpl in *; eauto using sem_var_In.
    Qed.

  End props.

  (** ** Restriction *)

  Fact sem_var_restrict : forall vars H id v,
      List.In id vars ->
      sem_var H id v ->
      sem_var (FEnv.restrict H vars) id v.
  Proof.
    intros * HIn Hsem.
    inv Hsem.
    econstructor; eauto.
    apply FEnv.restrict_find; auto.
  Qed.

  Fact sem_var_restrict_inv : forall vars H id v,
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

  Fact sem_clock_restrict : forall vars ck H bs bs',
      wx_clock vars ck ->
      sem_clock H bs ck bs' ->
      sem_clock (FEnv.restrict H (List.map fst vars)) bs ck bs'.
  Proof.
    intros * Hwc Hsem.
    eapply sem_clock_refines'; [eauto| |eauto].
    intros ?? Hinm Hvar.
    eapply sem_var_restrict; eauto.
    inv Hinm. now apply fst_InMembers.
  Qed.

  Fact sem_exp_restrict {PSyn prefs} : forall (G : @global PSyn prefs) Γ H Hl b e vs,
      wx_exp Γ e ->
      sem_exp G (H, Hl) b e vs ->
      sem_exp G (FEnv.restrict H (List.map fst Γ), Hl) b e vs.
  Proof with eauto with datatypes.
    induction e using exp_ind2; intros vs Hwt Hsem; inv Hwt; inv Hsem;
      econstructor; eauto; simpl_Forall; eauto.
    1-3:(eapply sem_var_restrict; eauto; apply fst_InMembers;
         take (IsVar _ _) and inv it; auto).
    1-3:(eapply Forall2Brs_impl_In; [|eauto]; intros ?? Hin Hse;
         simpl_Exists; simpl_Forall; eauto).
    specialize (H8 _ eq_refl). simpl_Forall; eauto.
  Qed.

  Lemma sem_equation_restrict {PSyn prefs} : forall (G : @global PSyn prefs) Γ H Hl b eq,
      wx_equation Γ eq ->
      sem_equation G (H, Hl) b eq ->
      sem_equation G (FEnv.restrict H (List.map fst Γ), Hl) b eq.
  Proof with eauto with datatypes.
    intros G ?? ? b [xs es] Hwc Hsem.
    destruct Hwc as (?&?). inv Hsem.
    econstructor. instantiate (1:=ss).
    + simpl_Forall; eauto.
      eapply sem_exp_restrict...
    + simpl_Forall; eauto.
      eapply sem_var_restrict...
      inv H1. now apply fst_InMembers.
  Qed.

  Fact sem_transitions_restrict {PSyn prefs} : forall (G : @global PSyn prefs) Γ H Hl b trans default stres,
      Forall (fun '(e, _) => wx_exp Γ e) trans ->
      sem_transitions G (H, Hl) b trans default stres ->
      sem_transitions G (FEnv.restrict H (List.map fst Γ), Hl) b trans default stres.
  Proof with eauto.
    induction trans; intros * Hwx Hsem; inv Hwx; inv Hsem;
      econstructor; eauto using sem_exp_restrict.
  Qed.

  Lemma sem_scope_restrict {A} (wx_block : _ -> _ -> Prop) (sem_block : _ -> _ -> Prop) {PSyn prefs} (G: @global PSyn prefs) :
    forall Γ Hi Hl bs locs caus (blks : A),
      (forall Γ Hi Hl, wx_block Γ blks -> sem_block (Hi, Hl) blks -> sem_block (FEnv.restrict Hi (List.map fst Γ), Hl) blks) ->
      wx_scope wx_block Γ (Scope locs caus blks) ->
      sem_scope (fun Hi' => sem_exp G Hi' bs) sem_block (Hi, Hl) bs (Scope locs caus blks) ->
      sem_scope (fun Hi' => sem_exp G Hi' bs) sem_block (FEnv.restrict Hi (List.map fst Γ), Hl) bs (Scope locs caus blks).
  Proof.
    intros * Hp Hwx Hsem; inv Hwx; inv Hsem.
    eapply Sscope with (Hi':=FEnv.restrict Hi' (List.map fst (Γ ++ senv_of_locs locs))); eauto.
    - intros * Hsem Hnin.
      eapply sem_var_restrict_inv in Hsem as (Hin&Hsem).
      eapply sem_var_restrict; eauto.
      simpl_app. apply in_app_iff in Hin as [Hin|Hin]; auto.
      setoid_rewrite map_fst_senv_of_locs in Hin.
      exfalso. apply Hnin, fst_InMembers; auto.
    - intros * Hin. edestruct H9; eauto. destruct_conjs.
      simpl_Forall.
      do 3 esplit. repeat split; eauto.
      eapply sem_exp_restrict; eauto.
      eapply sem_var_restrict; eauto. simpl_app. apply in_or_app. right. solve_In.
  Qed.

  Lemma sem_block_restrict {PSyn prefs} : forall (G: @global PSyn prefs) blk Γ H Hl b,
      wx_block Γ blk ->
      sem_block G (H, Hl) b blk ->
      sem_block G (FEnv.restrict H (List.map fst Γ), Hl) b blk.
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
      + instantiate (1:=(_,_)). destruct H2 as (Href1&Href2); split; simpl in *; [|eauto].
        intros ?? Hfind. apply FEnv.restrict_find_inv in Hfind as (Hin&Hfind).
        eapply Href1 in Hfind as (?&Hfilter&Hfind').
        do 2 esplit; eauto using FEnv.restrict_find.
      + destruct s. eapply sem_scope_restrict; eauto.
        intros; simpl_Forall; eauto.
    - (* automaton (weak transitions) *)
      econstructor; eauto.
      + eapply sem_clock_restrict; eauto.
      + eapply sem_transitions_restrict; eauto. simpl_Forall; auto.
      + simpl_Forall. specialize (H16 k); destruct_conjs.
        esplit; split.
        * instantiate (1:=(_,_)). destruct H4 as (Href1&Href2); split; simpl in *; [|eauto].
          intros ?? Hfind. apply FEnv.restrict_find_inv in Hfind as (Hin&Hfind).
          eapply Href1 in Hfind as (?&Hfilter&Hfind').
          do 2 esplit; eauto using FEnv.restrict_find.
        * destruct s; destruct_conjs. eapply sem_scope_restrict; eauto.
          intros * (?&?) (?&?); split; simpl_Forall; eauto using sem_transitions_restrict.
    - (* automaton (strong transitions) *)
      econstructor; eauto.
      + eapply sem_clock_restrict; eauto.
      + simpl_Forall. specialize (H15 k); destruct_conjs.
        esplit; split.
        * instantiate (1:=(_,_)). destruct H4 as (Href1&Href2); split; simpl in *; [|eauto].
          intros ?? Hfind. apply FEnv.restrict_find_inv in Hfind as (Hin&Hfind).
          eapply Href1 in Hfind as (?&Hfilter&Hfind').
          do 2 esplit; eauto using FEnv.restrict_find.
        * eauto using sem_transitions_restrict.
      + simpl_Forall. specialize (H16 k); destruct_conjs.
        esplit; split.
        * instantiate (1:=(_,_)). destruct H4 as (Href1&Href2); split; simpl in *; [|eauto].
          intros ?? Hfind. apply FEnv.restrict_find_inv in Hfind as (Hin&Hfind).
          eapply Href1 in Hfind as (?&Hfilter&Hfind').
          do 2 esplit; eauto using FEnv.restrict_find.
        * destruct s; destruct_conjs. eapply sem_scope_restrict; eauto.
          intros; simpl_Forall; eauto.
    - (* locals *)
      constructor. eapply sem_scope_restrict; eauto.
      intros; simpl_Forall; eauto.
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

  Lemma fby_aligned : forall bs xs ys zs,
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

  Corollary sem_automaton_wt_state1 {PSyn prefs A} (G : @global PSyn prefs) (states : list ((enumtag * ident) * (list transition * scope (A * list transition)))) :
    forall Hi bs bs' ini oth stres0 stres1 stres,
      Permutation.Permutation (List.map fst (List.map fst states)) (seq 0 (Datatypes.length states)) ->
      Forall (fun '(_, t) => InMembers t (List.map fst states)) ini ->
      In oth (seq 0 (Datatypes.length states)) ->
      Forall (fun '(_, (_, Scope _ _ (_, trans))) =>
                Forall (fun '(e, (t, _)) => InMembers t (List.map fst states)) trans) states ->
      sem_transitions G Hi bs' (List.map (fun '(e, t) => (e, (t, false))) ini) (oth, false) stres0 ->
      fby stres0 stres1 stres ->
      Forall (fun '((sel, _), (_, Scope _ _ (_, trans))) =>
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
    { simpl_Forall. destruct s; destruct_conjs. specialize (Hsemst k); destruct_conjs.
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
      specialize (Hwt1 ((count (ffilterb e (stres_st stres) (stres_res stres))) # m)).
      apply SForall_forall with (n:=m) in Hwt1.
      unfold fselect in Hwt1. rewrite mask_nth, Nat.eqb_refl, ffilter_nth in Hwt1.
      unfold stres_st in Hwt1. rewrite Str_nth_map, Hres, equiv_decb_refl in Hwt1.
      auto.
  Qed.

  Corollary sem_automaton_wt_state2 {PSyn prefs A} (G : @global PSyn prefs) (states : list ((enumtag * ident) * (list transition * scope (A * list transition)))) :
    forall bs bs' ini stres1 stres,
      Permutation.Permutation (List.map fst (List.map fst states)) (seq 0 (Datatypes.length states)) ->
      In ini (seq 0 (Datatypes.length states)) ->
      Forall (fun '(_, (trans, _)) =>
                Forall (fun '(e, (t, _)) => InMembers t (List.map fst states)) trans) states ->
      fby (const_stres bs' (ini, false)) stres1 stres ->
      Forall (fun '((sel, _), (trans, _)) =>
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
    { simpl_Forall. destruct s; destruct_conjs. specialize (Hsemst k); destruct_conjs.
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
      specialize (Hwt1 ((count (ffilterb n0 (stres_st stres) (stres_res stres))) # m)).
      apply SForall_forall with (n:=m) in Hwt1.
      unfold fselect in Hwt1. rewrite mask_nth, Nat.eqb_refl, ffilter_nth in Hwt1.
      eapply eq_ind with (P:=fun x => match x with absent => True | present (e0, _) => _ end) in Hwt1.
      2:{ unfold stres_st. rewrite Str_nth_map. setoid_rewrite Hres. rewrite equiv_decb_refl. reflexivity. }
      assumption.
  Qed.

  Corollary sem_automaton_wt_state3 {PSyn prefs A} (G : @global PSyn prefs) (states : list ((enumtag * ident) * (list transition * scope (A * list transition)))) :
    forall bs bs' ini stres1 stres,
      Permutation.Permutation (List.map fst (List.map fst states)) (seq 0 (Datatypes.length states)) ->
      In ini (seq 0 (Datatypes.length states)) ->
      Forall (fun '(_, (trans, _)) =>
                Forall (fun '(e, (t, _)) => InMembers t (List.map fst states)) trans) states ->
      fby (const_stres bs' (ini, false)) stres1 stres ->
      Forall (fun '((sel, _), (trans, _)) =>
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
    { simpl_Forall. destruct s; destruct_conjs. specialize (Hsemst k); destruct_conjs.
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
    specialize (Hwt1 ((count (ffilterb n0 (stres_st stres) (stres_res stres))) # n)).
    apply SForall_forall with (n:=n) in Hwt1.
    unfold fselect in Hwt1. rewrite mask_nth, Nat.eqb_refl, ffilter_nth in Hwt1.
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
