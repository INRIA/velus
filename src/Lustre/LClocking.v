From Velus Require Import Common.
From Velus Require Import Environment.
From Velus Require Import Operators.
From Velus Require Import Clocks.
From Velus Require Import Lustre.LSyntax.

From Coq Require Import List.
Import List.ListNotations.
Open Scope list_scope.

From Coq Require Import Morphisms.
From Coq Require Import Permutation.

From Coq Require Import Program.Basics.
Open Scope program_scope.

(** * Lustre clocking *)

(**

  Clocking judgements for Lustre.
  Classify Lustre programs which are statically well-formed.

 *)

Module Type LCLOCKING
       (Import Ids  : IDS)
       (Import Op   : OPERATORS)
       (Import Syn  : LSYNTAX Ids Op).

  (* TODO: Update this comment after recent changes *)
  (** Substitutions and conversion between clock types.

      The clocking of function applications is complicated by the possibility
      of 'anonymous' variables and their clocks.

      Consider, for instance, the two node (clock) interfaces
          f (a :: .; b :: . on a) returns (w :: .; x :: . on w)
          g (c :: .; d :: . on c) returns (y :: .; z :: . on y)

       and the equation
          u, v = g(f(b, e when b))

       The input parameters of f and their clocks are instantiated from
       the expressions; f yields two streams and the second one is dependent
       on the first. This dependency needs to be captured and verified in
       the application of g. The problem is that these intermediate flows
       are not bound to variable names in the environment.

       To treat this detail, we introduce "stream clocks" (sclock) that have
       the same structure as normal clocks but whose variables are either
       variables named in the environment (Vnm) or created as fresh variables
       to name the outputs of a node (Vidx). Clock annotations within
       expressions are then made with "named clocks" (nclock) that are either
       anonymous stream clocks (Cstream) or named stream clocks (Cnamed).

       The structure of an expression can be seen as stacks of function
       applications rooted in an equation (a pattern binding of variable
       names to resulting streams):

                                            -e4-  -e5-
             -e1-  -e2-    -e3-             ----f3----
             ----f1----    -f2-       e6    ----f4----          -e8-  -e9-
             --------------------f5-------------------   -e7-   ----f6----
             =============================================================
             ----------(v, w,...----------------------   -,x-   --,y ,z)--

       The expressions at the tips are clocked in the node environment, thus
       any variables are directly named. Each function call, however, may
       introduce fresh clock names to track dependencies between node outputs
       and for checking dependencies at node inputs. Unlike for a named clock,
       the scope of a fresh clock is limited to its "column". The freshness
       of clocks is ensured by a constraint (DisjointIndexes).

       Three kinds of substitutions are needed to handle node applications and
       equation patterns:

       1. input substitutions: map some input parameter names to clock ids.
          For instance, in "f(t :: ck, e1 :: ck on t)", "f" must be
          instantiated with the input substitution "(ck, [ t / a ])", giving
          the base clock and variable mappings, before testing for equality
          of the clocks of the arguments, "[(t : ck); ck on t]", against the
          instantiated input parameters and clocks.

       2. output substitutions: map some output parameter names to fresh
          clock indexes. For instance, in the previous example, an output
          substitution for "f" could be "[ w / 1 ]" giving the output
          clocks "[(1 : ck); ck on 1]". The use of "1" is arbitrary, other
          valid substitutions would give "[(2: ck); ck on 2]" or
          "[(42 : ck); ck on 42]". Substitutions need only reflect clock
          dependencies and satisfy the freshness constraint whenever
          expression "branches" join.

       3. pattern substitutions: in an equation, the fresh clock indexes
          must be mapped to the variable names appearing in the lhs pattern.
          An unmapped index indicates an escaping clock and thus a clocking
          problem. In the example, we may have:
             f [(b:ck); ck on b] -> [(1:ck); ck on 1]
             g [(1:ck); ck on 1] -> [(2:ck); ck on 2]

          and thus "[(2:ck); ck on 2]" must be unified with
          "[(u:ck); ck on u]", and the required substitution is "[ u / 2 ]".
   *)

  (* substitution of identifiers *)
  Definition ident_map := ident -> option ident.

  (* xc : name and clock from the node interface
     nc : named clock from the annotated expression *)
  Definition WellInstantiated (bck : clock) (sub : ident_map)
                              (xc : ident * clock) (nc : nclock) : Prop :=
    sub (fst xc) = snd nc
    /\ instck bck sub (snd xc) = Some (fst nc).

  Section WellClocked.

    Variable G    : global.
    Variable vars : list (ident * clock).

    Inductive wc_exp : exp -> Prop :=
    | wc_Econst: forall c,
        wc_exp (Econst c)

    | wc_Evar: forall x ty ck,
        In (x, ck) vars ->
        wc_exp (Evar x (ty, (ck, Some x)))

    | wc_Eunop: forall op e ty ck,
        wc_exp e ->
        clockof e = [ck] ->
        wc_exp (Eunop op e (ty, (ck, None)))

    | wc_Ebinop: forall op e1 e2 ty ck,
        wc_exp e1 ->
        wc_exp e2 ->
        clockof e1 = [ck] ->
        clockof e2 = [ck] ->
        wc_exp (Ebinop op e1 e2 (ty, (ck, None)))

    | wc_Efby: forall e0s es anns,
        Forall wc_exp e0s ->
        Forall wc_exp es ->
        Forall2 eq (map clock_of_nclock anns) (clocksof e0s) ->
        Forall2 eq (map clock_of_nclock anns) (clocksof es) ->
        Forall unnamed_stream anns ->
        wc_exp (Efby e0s es anns)

    | wc_Ewhen: forall es x b tys ck,
        Forall wc_exp es ->
        In (x, ck) vars ->
        Forall (eq ck) (clocksof es) ->
        length tys = length (clocksof es) ->
        wc_exp (Ewhen es x b (tys, (Con ck x b, None)))

    | wc_Emerge: forall x ets efs tys ck,
        Forall wc_exp ets ->
        Forall wc_exp efs ->
        In (x, ck) vars ->
        Forall (eq (Con ck x true))  (clocksof ets) ->
        Forall (eq (Con ck x false)) (clocksof efs) ->
        length tys = length (clocksof ets) ->
        length tys = length (clocksof efs) ->
        wc_exp (Emerge x ets efs (tys, (ck, None)))

    | wc_Eifte: forall e ets efs tys ck,
        wc_exp e ->
        Forall wc_exp ets ->
        Forall wc_exp efs ->
        clockof e = [ck] ->
        Forall (eq ck) (clocksof ets) ->
        Forall (eq ck) (clocksof efs) ->
        length tys = length (clocksof ets) ->
        length tys = length (clocksof efs) ->
        0 < length tys ->
        wc_exp (Eite e ets efs (tys, (ck, None)))

    | wc_Eapp: forall f es anns n bck sub,
        Forall wc_exp es ->
        find_node f G = Some n ->
        Forall2 (WellInstantiated bck sub) (idck n.(n_in)) (nclocksof es) ->
        Forall2 (WellInstantiated bck sub) (idck n.(n_out)) (map snd anns) ->
        wc_exp (Eapp f es None anns)

    | wc_EappReset: forall f es r ckr anns n bck sub,
        Forall wc_exp es ->
        find_node f G = Some n ->
        Forall2 (WellInstantiated bck sub) (idck n.(n_in)) (nclocksof es) ->
        Forall2 (WellInstantiated bck sub) (idck n.(n_out)) (map snd anns) ->
        wc_exp r ->
        clockof r = [ckr] ->
        (* TODO: clock of r *)
        wc_exp (Eapp f es (Some r) anns).

    Inductive Is_fresh_in : ident -> exp -> Prop :=
    | IFEunop: forall x op e ann,
        Is_fresh_in x e ->
        Is_fresh_in x (Eunop op e ann)

    | IFEbinop: forall x op e1 e2 ann,
        Is_fresh_in x e1 \/ Is_fresh_in x e2 ->
        Is_fresh_in x (Ebinop op e1 e2 ann)

    | IFEfby: forall x e0s es anns,
        Exists (Is_fresh_in x) (e0s ++ es) ->
        Is_fresh_in x (Efby e0s es anns)

    | IFEwhen: forall x es y b anns,
        Exists (Is_fresh_in x) es ->
        Is_fresh_in x (Ewhen es y b anns)

    | IFEmerge: forall x ets efs y anns,
        Exists (Is_fresh_in x) (ets ++ efs) ->
        Is_fresh_in x (Emerge y ets efs anns)

    | IFEifte: forall x e ets efs anns,
        Exists (Is_fresh_in x) (e :: (ets ++ efs)) ->
        Is_fresh_in x (Eite e ets efs anns)

    | IFEapp: forall x f es anns,
        Exists (Is_fresh_in x) es
        \/ Ino x (map stream_name anns) ->
        Is_fresh_in x (Eapp f es None anns)

    | IFEreset: forall x f es e anns,
        Exists (Is_fresh_in x) (e :: es)
        \/ Ino x (map stream_name anns) ->
        Is_fresh_in x (Eapp f es (Some e) anns).

    Inductive DisjointFreshList : list exp -> Prop :=
    | DWnil:
        DisjointFreshList []

    | DWcons: forall e es,
        DisjointFreshList es ->
        (forall x, Is_fresh_in x e -> ~Exists (Is_fresh_in x) es) ->
        DisjointFreshList (e::es).

    Definition Is_AnonStream (x : option ident) : Prop :=
      match x with
      | None => True
      | Some x => ~ InMembers x vars
      end.

    Inductive DisjointFresh : exp -> Prop :=
    | DFEconst: forall c,
        DisjointFresh (Econst c)

    | DFEvar: forall x ann,
        DisjointFresh (Evar x ann)

    | DFEunop: forall op e ann,
        DisjointFresh e ->
        DisjointFresh (Eunop op e ann)

    | DFEbinop: forall op e1 e2 ann,
        DisjointFresh e1 ->
        DisjointFresh e2 ->
        (forall x, Is_fresh_in x e1 -> ~Is_fresh_in x e2) ->
        DisjointFresh (Ebinop op e1 e2 ann)

    | DFEfby: forall e0s es anns,
        DisjointFreshList (e0s ++ es) ->
        Forall DisjointFresh (e0s ++ es) ->
        DisjointFresh (Efby e0s es anns)

    | DFEwhen: forall es x b anns,
        DisjointFreshList es ->
        Forall DisjointFresh es ->
        DisjointFresh (Ewhen es x b anns)

    | DFEmerge: forall x ets efs anns,
        DisjointFreshList (ets ++ efs) ->
        Forall DisjointFresh (ets ++ efs) ->
        DisjointFresh (Emerge x ets efs anns)

    | DFEifte: forall e ets efs anns,
        DisjointFreshList (e :: (ets ++ efs)) ->
        Forall DisjointFresh (e :: (ets ++ efs)) ->
        DisjointFresh (Eite e ets efs anns)

    | DFEapp: forall f es anns,
        DisjointFreshList es ->
        Forall DisjointFresh es ->
        NoDupo (map stream_name anns) ->
        Forall Is_AnonStream (map stream_name anns) ->
        (forall x, Ino x (map stream_name anns) -> ~Exists (Is_fresh_in x) es) ->
        DisjointFresh (Eapp f es None anns)

    | DFEreset: forall f es e anns,
        DisjointFreshList (e :: es) ->
        Forall DisjointFresh (e :: es) ->
        NoDupo (map stream_name anns) ->
        Forall Is_AnonStream (map stream_name anns) ->
        (forall x, Ino x (map stream_name anns) -> ~Exists (Is_fresh_in x) (e :: es)) ->
        DisjointFresh (Eapp f es (Some e) anns).

    Definition WellFormedAnon (e : exp) : Prop :=
      match e with
      | Eapp f es None anns => Forall DisjointFresh es /\ DisjointFreshList es
      | Eapp f es (Some r) anns =>
        Forall DisjointFresh (r :: es) /\ DisjointFreshList (r :: es)
      | _ => DisjointFresh e
      end.

    Definition wc_equation (xses : equation) : Prop :=
      let (xs, es) := xses in
      Forall wc_exp es
      /\ Forall WellFormedAnon es
      /\ Forall2 (fun x nc => LiftO True (eq x) (snd nc)) xs (nclocksof es)
      /\ Forall2 (fun x ck => In (x, ck) vars) xs (clocksof es).

  End WellClocked.

  Definition wc_node (G: global) (n: node) : Prop
    :=    wc_env (idck  n.(n_in))
       /\ wc_env (idck (n.(n_in) ++ n.(n_out)))
       /\ wc_env (idck (n.(n_in) ++ n.(n_out) ++ n.(n_vars)))
       /\ Forall (wc_equation G (idck (n.(n_in) ++ n.(n_vars) ++ n.(n_out))))
                 n.(n_eqs).

  Inductive wc_global : global -> Prop :=
  | wcg_nil:
      wc_global []
  | wcg_cons: forall n ns,
      wc_global ns ->
      wc_node ns n ->
      Forall (fun n'=> n.(n_name) <> n'.(n_name) :> ident) ns ->
      wc_global (n::ns).

  (** ** Basic properties of clocking *)

  Hint Constructors wc_exp wc_global : lclocking.
  Hint Unfold wc_equation wc_node wc_env : lclocking.

  Section wc_exp_ind2.

    Variable G    : global.
    Variable vars : list (ident * clock).
    Variable P : exp -> Prop.

    Hypothesis EconstCase:
      forall c : const,
        P (Econst c).

    Hypothesis EvarCase:
      forall x ty ck,
        In (x, ck) vars ->
        P (Evar x (ty, (ck, Some x))).

    Hypothesis EunopCase:
      forall op e ty ck,
        wc_exp G vars e ->
        P e ->
        clockof e = [ck] ->
        P (Eunop op e (ty, (ck, None))).

    Hypothesis EbinopCase:
      forall op e1 e2 ty ck,
        wc_exp G vars e1 ->
        P e1 ->
        wc_exp G vars e2 ->
        P e2 ->
        clockof e1 = [ck] ->
        clockof e2 = [ck] ->
        P (Ebinop op e1 e2 (ty, (ck, None))).

    Hypothesis EfbyCase:
      forall e0s es anns,
        Forall (wc_exp G vars) e0s ->
        Forall (wc_exp G vars) es ->
        Forall P es ->
        Forall P e0s ->
        Forall2 eq (map clock_of_nclock anns) (clocksof e0s) ->
        Forall2 eq (map clock_of_nclock anns) (clocksof es) ->
        Forall unnamed_stream anns ->
        P (Efby e0s es anns).

    Hypothesis EwhenCase:
      forall es x b tys ck,
        Forall (wc_exp G vars) es ->
        Forall P es ->
        In (x, ck) vars ->
        Forall (eq ck) (clocksof es) ->
        length tys = length (clocksof es) ->
        P (Ewhen es x b (tys, (Con ck x b, None))).

    Hypothesis EmergeCase:
      forall x ets efs tys ck,
        Forall (wc_exp G vars) ets ->
        Forall P ets ->
        Forall (wc_exp G vars) efs ->
        Forall P efs ->
        In (x, ck) vars ->
        Forall (eq (Con ck x true))  (clocksof ets) ->
        Forall (eq (Con ck x false)) (clocksof efs) ->
        length tys = length (clocksof ets) ->
        length tys = length (clocksof efs) ->
        P (Emerge x ets efs (tys, (ck, None))).

    Hypothesis EiteCase:
      forall e ets efs tys ck,
        wc_exp G vars e ->
        P e ->
        Forall (wc_exp G vars) ets ->
        Forall P ets ->
        Forall (wc_exp G vars) efs ->
        Forall P efs ->
        clockof e = [ck] ->
        Forall (eq ck)  (clocksof ets) ->
        Forall (eq ck) (clocksof efs) ->
        length tys = length (clocksof ets) ->
        length tys = length (clocksof efs) ->
        0 < length tys ->
        P (Eite e ets efs (tys, (ck, None))).

    Hypothesis EappCase:
      forall f es anns n bck sub,
        Forall (wc_exp G vars) es ->
        Forall P es ->
        find_node f G = Some n ->
        Forall2 (WellInstantiated bck sub) (idck n.(n_in)) (nclocksof es) ->
        Forall2 (WellInstantiated bck sub) (idck n.(n_out)) (map snd anns) ->
        P (Eapp f es None anns).

    Hypothesis EappResetCase:
      forall f es r ckr anns n bck sub,
        Forall (wc_exp G vars) es ->
        Forall P es ->
        find_node f G = Some n ->
        Forall2 (WellInstantiated bck sub) (idck n.(n_in)) (nclocksof es) ->
        Forall2 (WellInstantiated bck sub) (idck n.(n_out)) (map snd anns) ->
        wc_exp G vars r ->
        clockof r = [ckr] ->
        P r ->
        P (Eapp f es (Some r) anns).

    Fixpoint wc_exp_ind2 (e: exp) (H: wc_exp G vars e) {struct H} : P e.
    Proof.
      destruct H; eauto.
      - apply EfbyCase; auto.
        + clear H2. induction H0; auto.
        + clear H1. induction H; auto.
      - apply EwhenCase; auto.
        clear H1 H2. induction H; auto.
      - apply EmergeCase; auto.
        clear H2 H4. induction H; auto.
        clear H3 H5. induction H0; auto.
      - apply EiteCase; auto.
        clear H3 H5. induction H0; auto.
        clear H4 H6. induction H1; auto.
      - eapply EappCase; eauto.
        clear H0 H1. induction H; eauto.
      - eapply EappResetCase; eauto.
        clear H0 H1 H2. induction H; eauto.
    Qed.

  End wc_exp_ind2.

  Lemma wc_global_app:
    forall G G',
      wc_global (G' ++ G) ->
      wc_global G.
  Proof.
    induction G'; auto.
    simpl. intro Hwc.
    inversion Hwc; auto.
  Qed.

  Lemma wc_find_node:
    forall G f n,
      wc_global G ->
      find_node f G = Some n ->
      exists G', wc_node G' n.
  Proof.
    intros G f n' Hwc Hfind.
    apply find_node_split in Hfind.
    destruct Hfind as (bG & aG & HG).
    subst. apply wc_global_app in Hwc.
    inversion Hwc. eauto.
  Qed.

  Lemma indexes_app:
    forall xs ys,
      indexes (xs ++ ys) = indexes xs ++ indexes ys.
  Proof.
    induction xs as [|x xs IH]. reflexivity.
    destruct x; simpl; auto.
    destruct o; simpl; auto.
    now setoid_rewrite IH.
  Qed.

  Instance wc_exp_Proper:
    Proper (@eq global ==> @Permutation.Permutation (ident * clock)
                ==> @eq exp ==> iff)
           wc_exp.
  Proof.
    intros G G' HG env' env Henv e' e He.
    rewrite HG, He. clear HG He.
    split; intro H;
      induction H using wc_exp_ind2;
      (rewrite Henv in * || rewrite <-Henv in * || idtac);
      eauto with lclocking.
  Qed.

  Instance wc_exp_pointwise_Proper:
    Proper (@eq global ==> @Permutation.Permutation (ident * clock)
                ==> pointwise_relation _ iff)
           wc_exp.
  Proof.
    intros G G' HG env' env Henv e.
    now rewrite Henv, HG.
  Qed.

  Instance Is_AnonStream_pointwise_Proper:
    Proper (@Permutation.Permutation (ident * clock) ==> pointwise_relation _ iff)
           Is_AnonStream.
  Proof.
    intros G' G EG xo.
    unfold Is_AnonStream; destruct xo; [now rewrite EG|now intuition].
  Qed.

  Instance Is_AnonStream_Proper:
    Proper (@Permutation.Permutation (ident * clock) ==> eq ==> iff)
           Is_AnonStream.
  Proof.
    intros G' G EG xo' xo Exo; subst.
    unfold Is_AnonStream; destruct xo; [now rewrite EG|now intuition].
  Qed.

  Instance DisjointFresh_pointwise_Proper:
    Proper (@Permutation.Permutation (ident * clock) ==> pointwise_relation _ iff)
           DisjointFresh.
  Proof.
    intros G' G EG e.
    Local Hint Extern 4 (Forall _ (_ ++ _)) => apply Forall_app.
    induction e using exp_ind2; split; inversion 1; subst;
      repeat match goal with
             | H:_ <-> _ |- _ => destruct H
             | H:Forall (fun e => _ e <-> _ e) _ |- _ => apply Forall_iff_insideout in H
             | H:Forall _ (_ ++ _) |- _ => apply Forall_app in H as (? & ?)
             | H:Forall _ (_ :: _) |- _ => apply Forall_hd_tl in H as (? & ?)
             | H:Forall (Is_AnonStream G') _ |- DisjointFresh G _ => rewrite EG in H
             | H:Forall (Is_AnonStream G) _ |- DisjointFresh G' _ => rewrite <-EG in H
             end;
      eauto 8 using DisjointFresh.
  Qed.

  Instance DisjointFresh_Proper:
    Proper (@Permutation.Permutation (ident * clock) ==> eq ==> iff)
           DisjointFresh.
  Proof.
    intros G' G EG e' e Ee; subst.
    induction e using exp_ind2; split; inversion 1; subst;
      repeat match goal with
             | H:_ <-> _ |- _ => destruct H
             | H:Forall (fun e => _ e <-> _ e) _ |- _ => apply Forall_iff_insideout in H
             | H:Forall _ (_ ++ _) |- _ => apply Forall_app in H as (? & ?)
             | H:Forall _ (_ :: _) |- _ => apply Forall_hd_tl in H as (? & ?)
             | H:Forall (Is_AnonStream G') _ |- DisjointFresh G _ => rewrite EG in H
             | H:Forall (Is_AnonStream G) _ |- DisjointFresh G' _ => rewrite <-EG in H
             end;
      eauto 8 using DisjointFresh.
  Qed.

  Instance WellFormedAnon_Proper:
    Proper (@Permutation.Permutation (ident * clock) ==> eq ==> iff)
           WellFormedAnon.
  Proof.
    intros G' G EG e' e Ee; subst.
    unfold WellFormedAnon.
    destruct e; try rewrite EG; intuition.
    now destruct o; rewrite EG in *; intuition.
    now destruct o; rewrite EG; intuition.
  Qed.

  Instance WellFormedAnon_pointwise_Proper:
    Proper (@Permutation.Permutation (ident * clock) ==> pointwise_relation _ iff)
           WellFormedAnon.
  Proof.
    intros env' env Henv e. now rewrite Henv.
  Qed.

  Instance wc_equation_Proper:
    Proper (@eq global ==> @Permutation.Permutation (ident * clock)
                ==> @eq equation ==> iff)
           wc_equation.
  Proof.
    intros G1 G2 HG env1 env2 Henv eq1 eq2 Heq; subst.
    destruct eq2 as (xs & es). unfold wc_equation. rewrite Henv.
    split.
    - intros (HA & HB & HC & HD).
      repeat split; auto.
      now setoid_rewrite Henv in HD.
    - intros (HA & HB & HC & HD).
      repeat split; auto.
      now setoid_rewrite <-Henv in HD.
  Qed.

  Instance wc_equation_pointwise_Proper:
    Proper (@eq global ==> @Permutation.Permutation (ident * clock)
                ==> pointwise_relation _ iff)
           wc_equation.
  Proof.
    intros G1 G2 HG env1 env2 Henv eq; subst. now rewrite Henv.
  Qed.

  Lemma wc_env_has_Cbase':
    forall vars x xck,
      wc_env vars ->
      In (x, xck) vars ->
      exists y, In (y, Cbase) vars.
  Proof.
    intros vars x xck WC Ix.
    revert x Ix. induction xck; eauto.
    intros; eapply Forall_forall in WC; eauto.
    inv WC; eauto.
  Qed.

  Lemma wc_env_has_Cbase:
    forall vars,
      wc_env vars ->
      0 < length vars ->
      exists y, In (y, Cbase) vars.
  Proof.
    intros * Hwc Hl. destruct vars. now inv Hl.
    destruct p. eapply wc_env_has_Cbase'; eauto. now left.
  Qed.

  Lemma WellInstantiated_parent :
    forall bck sub cks lck,
      Forall2 (WellInstantiated bck sub) cks lck ->
      Forall (fun ck => fst ck = bck \/ clock_parent bck (fst ck)) lck.
  Proof.
    intros. apply Forall_forall. intros * Hin.
    pose proof (Forall2_in_right _ _ _ _ H Hin) as (?&?&?&?).
    eauto using instck_parent.
  Qed.

  Lemma WellInstantiated_bck :
    forall vars bck sub lck,
      wc_env vars ->
      0 < length vars ->
      Forall2 (WellInstantiated bck sub) vars lck ->
      In bck (map stripname lck).
  Proof.
    intros * Henv Hlen Wi.
    apply wc_env_has_Cbase in Henv as [x Hin]; auto.
    pose proof (Forall2_in_left _ _ _ _ Wi Hin) as (nc &?&?& He).
    simpl in *. apply in_map_iff. exists nc. destruct nc. simpl in *.
    now inv He.
  Qed.

  (** Validation *)

  Module OpAux := OperatorsAux Op.

  (* TODO: Move elsewhere? *)
  Local Ltac DestructMatch :=
    repeat progress
           match goal with
           | H:match ?e with _ => _ end = _ |- _ =>
             let Heq := fresh "Heq" in
             destruct e eqn:Heq; try discriminate
           end.

  (* TODO: add to a database *)
  Hint Extern 2 (In _ (idck _)) => apply In_idck_exists.

  Section ValidateExpression.

    Variable G : global.
    Variable venv : Env.t (type * clock).

    Open Scope option_monad_scope.

    Function check_var (x : ident) (ck : clock) : bool :=
      match Env.find x venv with
      | None => false
      | Some (_, xc) => ck ==b xc
      end.

    Definition check_paired_clocks (nc1 nc2 : nclock) (tc : ann) : bool :=
      match tc with
      | (t, (c, None)) => (fst nc1 ==b c) && (fst nc2 ==b c)
      | _ => false
      end.

    Function check_merge_clocks {A} (x : ident) (ck : clock) (nc1 nc2 : nclock) (ty : A) : bool :=
      match nc1, nc2 with
      | (Con ck1 x1 true, _), (Con ck2 x2 false, _) =>
        (ck1 ==b ck) && (ck2 ==b ck) && (x1 ==b x) && (x2 ==b x)
      | _, _ => false
      end.

    Function check_ite_clocks {A} (ck : clock) (nc1 nc2 : nclock) (ty : A) : bool :=
      (fst nc1 ==b ck) && (fst nc2 ==b ck).

    Definition add_isub
               (sub : Env.t ident)
               (nin : (ident * (type * clock)))
               (nc : nclock) : Env.t ident :=
      match snd nc, nin with
      | Some y, (x, (xt, xc)) => Env.add x y sub
      | None, _ => sub
      end.

    Definition add_osub
               (sub : Env.t ident)
               (nin : (ident * (type * clock)))
               (tnc : type * nclock) : Env.t ident :=
      add_isub sub nin (snd tnc).

    Section CheckInst.
      Variables (bck : clock) (sub : Env.t ident).

      Fixpoint check_inst (ick ck : clock) : bool :=
        match ick with
        | Cbase => (ck ==b bck)
        | Con ick' x xb =>
          match ck, Env.find x sub with
          | Con ck' y yb, Some sx =>
            (yb ==b xb) && (y ==b sx) && (check_inst ick' ck')
          | _, _ => false
          end
        end.
    End CheckInst.

    Fixpoint find_base_clock (ick ck : clock) : option clock :=
      match ick with
      | Cbase => Some ck
      | Con ick' _ _ =>
        match ck with
        | Cbase => None
        | Con ck' _ _ => find_base_clock ick' ck'
        end
      end.

    Definition check_reset (rt : option (option (list nclock))) : bool :=
      match rt with
      | None => true
      | Some (Some [nckr]) => true
      | _ => false
      end.

    Lemma nclockof_clockof:
      forall e xs ys,
        nclockof e = xs ->
        ys = map fst xs ->
        clockof e = ys.
    Proof.
      intros e xs ys NC Hys; subst.
      now rewrite clockof_nclockof.
    Qed.

    Fixpoint check_exp (e : exp) : option (list nclock) :=
      match e with
      | Econst c => Some ([(Cbase, None)])

      | Evar x (xt, nc) =>
        match nc with
        | (xc, Some n) => if (check_var x xc) && (x ==b n) then Some [nc] else None
        | _ => None
        end

      | Eunop op e (xt, nc) =>
        match nc with
        | (xc, None) =>
          do nce <- assert_singleton (check_exp e);
          if xc ==b fst nce then Some [nc] else None
        | _ => None
        end

      | Ebinop op e1 e2 (xt, nc) =>
        match nc with
        | (xc, None) =>
          do nc1 <- assert_singleton (check_exp e1);
          do nc2 <- assert_singleton (check_exp e2);
          if (xc ==b fst nc1) && (xc ==b fst nc2) then Some [nc] else None
        | _ => None
        end

      | Efby e0s es anns =>
        do nc0s <- oconcat (map check_exp e0s);
        do ncs <- oconcat (map check_exp es);
        if forall3b check_paired_clocks nc0s ncs anns
        then Some (map snd anns) else None

      | Ewhen es x b (tys, nc) =>
        match nc with
        | (Con xc y yb, None) =>
          do nces <- oconcat (map check_exp es);
          if (x ==b y) && (b ==b yb) && (check_var x xc)
             && (forall2b (fun '(c, _) _ => equiv_decb xc c) nces tys)
          then Some (map (fun _ => nc) tys) else None
        | _ => None
        end

      | Emerge x e1s e2s (tys, (ck, None)) =>
        do nc1s <- oconcat (map check_exp e1s);
        do nc2s <- oconcat (map check_exp e2s);
        let nc' := (ck, None) in
        if check_var x ck && (forall3b (check_merge_clocks x ck) nc1s nc2s tys)
        then Some (map (fun _ => nc') tys) else None

      | Eite e e1s e2s (tys, (ck, None)) =>
        do nc1s <- oconcat (map check_exp e1s);
        do nc2s <- oconcat (map check_exp e2s);
        do (ce, _) <- assert_singleton (check_exp e);
        let nc' := (ck, None) in
        if (ce ==b ck) && (forall3b (check_ite_clocks ck) nc1s nc2s tys)
                       && (length tys <>b 0)
        then Some (map (fun _ => nc') tys) else None

      | Eapp f es ro anns =>
        do n <- find_node f G;
        do nces <- oconcat (map check_exp es);
        do nin0 <- option_map (fun '(_, (_, ck)) => ck) (hd_error n.(n_in));
        do nces0 <- option_map fst (hd_error nces);
        do bck <- find_base_clock nin0 nces0;
        let isub := fold_left2 add_isub n.(n_in) nces (Env.empty ident) in
        let sub := fold_left2 add_osub n.(n_out) anns isub in
        if (forall2b (fun '(_, (_, ck)) '(ck', _) => check_inst bck sub ck ck')
                     n.(n_in) nces)
           && (forall2b (fun '(_, (_, ck)) '(_, (ck', _)) => check_inst bck sub ck ck')
                        n.(n_out) anns)
           && (check_reset (option_map check_exp ro))
        then Some (map snd anns) else None

      | _ => None end.

    Definition assert_no_intersection (S1 S2 : PS.t) : option PS.t :=
      if PS.is_empty (PS.inter S1 S2) then Some (PS.union S1 S2) else None.

    Definition check_anon_name (ann : type * nclock) (U : PS.t) : option PS.t :=
      match snd (snd ann) with
      | None => Some U
      | Some x => if PS.mem x U || Env.mem x venv then None else Some (PS.add x U)
      end.

    Fixpoint check_disjoint_fresh (e : exp) : option PS.t :=
      match e with
      | Econst c => Some PS.empty
      | Evar x _ => Some PS.empty
      | Eunop op e _ => check_disjoint_fresh e
      | Ebinop op e1 e2 _ =>
        do F1 <- check_disjoint_fresh e1;
        do F2 <- check_disjoint_fresh e2;
        assert_no_intersection F1 F2
      | Efby e0s es anns =>
        do F0s <- omap check_disjoint_fresh e0s;
        do Fs <- omap check_disjoint_fresh es;
        let U := ofold_right assert_no_intersection (Some PS.empty) F0s in
        ofold_right assert_no_intersection U Fs
      | Ewhen es x b _ =>
        do Fs <- omap check_disjoint_fresh es;
        ofold_right assert_no_intersection (Some PS.empty) Fs
      | Emerge x ets efs _ =>
        do FTs <- omap check_disjoint_fresh ets;
        do FFs <- omap check_disjoint_fresh efs;
        let U := ofold_right assert_no_intersection (Some PS.empty) FTs in
        ofold_right assert_no_intersection U FFs
      | Eite e ets efs _ =>
        do F <- check_disjoint_fresh e;
        do FTs <- omap check_disjoint_fresh ets;
        do FFs <- omap check_disjoint_fresh efs;
        let U := ofold_right assert_no_intersection (Some F) FTs in
        ofold_right assert_no_intersection U FFs

      | Eapp f es ro anns =>
        do Fs <- omap check_disjoint_fresh es;
        let F := match ro with None => Some PS.empty | Some e => check_disjoint_fresh e end in
        let U := ofold_right assert_no_intersection F Fs in
        ofold_right check_anon_name U anns
      end.

    Definition check_wellformedanon (e : exp) : bool :=
      match e with
      | Eapp f es ro anns =>
        match omap check_disjoint_fresh es with
        | None => false
        | Some Fs =>
          let F := match ro with
                   | None => Some PS.empty
                   | Some e => check_disjoint_fresh e
                   end
          in
          isSome (ofold_right assert_no_intersection F Fs)
        end
      | _ => isSome (check_disjoint_fresh e)
      end.

    Definition check_wellformedanon_and_exp (e : exp) : option (list nclock) :=
      if check_wellformedanon e then check_exp e else None.

    Function check_nclock (x : ident) (nck : nclock) : bool :=
      let '(ck, nm) := nck in
      check_var x ck && (match nm with
                         | None => true
                         | Some n => n ==b x
                         end).

    Definition check_equation (eq : equation) : bool :=
      let '(xs, es) := eq in
      match oconcat (map check_wellformedanon_and_exp es) with
      | None => false
      | Some ncks => forall2b check_nclock xs ncks
      end.

    Lemma assert_no_intersection_correct:
      forall F S1 S2,
        assert_no_intersection S1 S2 = Some F ->
        F = PS.union S1 S2
        /\ PS.Empty (PS.inter S1 S2).
    Proof.
      unfold assert_no_intersection.
      intros S1 S2 F NI. DestructMatch; inv NI.
      auto using PSF.is_empty_2.
    Qed.

    Lemma ofold_right_assert_no_intersection:
      forall F Fs F',
        ofold_right assert_no_intersection (Some F) Fs = Some F' ->
        F' === (PSUnion (F::Fs))
        /\ DisjointSetList (F::Fs).
    Proof.
      induction Fs; simpl.
      now inversion_clear 1; split; auto using DisjointSetList; reflexivity.
      intros F' ANI. DestructMatch.
      specialize (IHFs _ eq_refl) as (? & ?).
      take (assert_no_intersection _ _ = Some _)
           and apply assert_no_intersection_correct in it as (? & ?); subst.
      take (PS.Equal _ _) and rewrite it.
      rewrite <-perm_swap, (PSUnion_cons _ (F::Fs)).
      split; [reflexivity|].
      constructor; auto. rewrite Forall_forall.
      intros S IS. apply In_PSUnion in IS.
      rewrite <-it in IS. now rewrite IS.
    Qed.

    Lemma DisjointFreshList_app:
      forall es1 es2,
        DisjointFreshList (es1 ++ es2)
        <-> (DisjointFreshList es1
           /\ DisjointFreshList es2
           /\ Forall (fun e => forall x, Is_fresh_in x e -> ~Exists (Is_fresh_in x) es2) es1).
    Proof.
      induction es1 as [|e es1 IH]; intro es2. now intuition constructor.
      rewrite <-app_comm_cons. split.
      - inversion 1 as [|?? DFL1 DFL2]; subst.
        apply IH in DFL1 as (DF1 & DF2 & DFC).
        setoid_rewrite Exists_app' in DFL2.
        setoid_rewrite not_or' in DFL2.
        repeat split; auto using DisjointFreshList; constructor; auto;
          now intros x FI; apply DFL2 in FI.
      - intros (DFL1 & DFL2 & DFC).
        inversion_clear DFL1 as [|?? DFL3 DFL4].
        apply Forall_hd_tl in DFC as (DFC1 & DFC2).
        constructor. now apply IH; intuition.
        intros x Fx. rewrite Exists_app', not_or'. firstorder.
    Qed.

    Lemma ofold_right_check_anon_name_correct:
      forall anns F F',
        ofold_right check_anon_name (Some F) anns = Some F' ->
        PS.Subset F F'
        /\ NoDupo (map stream_name anns)
        /\ Forall (Is_AnonStream (idck (Env.elements venv))) (map stream_name anns)
        /\ (forall x, Ino x (map stream_name anns) <-> ~PS.In x F /\ PS.In x F').
    Proof.
      induction anns as [|ann anns IH]; simpl.
      now inversion_clear 1;
        repeat split; eauto using NoDupo_nil, PSP.subset_refl; intuition.
      intros F F' OFR. DestructMatch.
      take (ofold_right check_anon_name _ _ = Some _)
           and apply IH in it as (SS & ND & FA & INO).
      destruct ann as (ty, (ck, nm)). destruct nm.
      - unfold check_anon_name in OFR; simpl in *.
        DestructMatch.
        take (_ || _ = false) and rewrite Bool.orb_false_iff, <-PSF.not_mem_iff,
                                         <-Env.Props.P.F.not_mem_in_iff in it.
        destruct it as (NI & NV). inv OFR. repeat split.
        + now rewrite SS; apply PSP.subset_add_2.
        + apply NoDupo_conss; auto.
          intro Ii; apply INO in Ii as (? & ?); auto.
        + constructor; auto. simpl.
          now rewrite InMembers_idck, <-Env.In_Members.
        + take (_ \/ _) and destruct it; subst; auto.
          now take (Ino _ _) and apply INO in it as (? & ?).
        + take (_ \/ _) and destruct it; subst; auto using PSF.add_1.
          take (Ino _ _) and apply INO in it as (? & ?); auto using PSF.add_2.
        + intros (Nx & Ix). apply PS.add_spec in Ix as [Ix|Ix]; auto.
          right. apply INO; auto.
      - inv OFR; unfold stream_name, Is_AnonStream; simpl.
        repeat split; auto using NoDupo_consn.
        + take (_ \/ _) and destruct it; try contradiction;
            now take (Ino _ _) and apply INO in it as (? & ?).
        + take (_ \/ _) and destruct it; try contradiction;
            now take (Ino _ _) and apply INO in it as (? & ?).
        + intros (Nx & Ix); right. apply INO; auto.
    Qed.

    Lemma Disjoint_Is_fresh_in_DisjointFreshList:
      forall es Fs,
        Forall2 (fun e F => forall x, Is_fresh_in x e <-> PS.In x F) es Fs ->
        DisjointSetList Fs ->
        DisjointFreshList es.
    Proof.
      induction es as [|e es IH]; auto using DisjointFreshList.
      intros Fs FA DL. destruct Fs as [|F Fs]; inv FA; inv DL.
      match goal with DJ:DisjointSetList Fs, FA:Forall2 _ _ _ |- _ =>
                      specialize (IH _ FA DJ) end.
      constructor; auto. intros x Fx.
      take (forall x, Is_fresh_in x _ <-> PS.In x _) and apply it in Fx.
      apply Forall_Exists_neg.
      take (Forall2 _ _ _) and apply Forall2_ignore2 in it.
      apply Forall_impl_In with (2:=it).
      intros e' Ie' (F' & IF' & HF') Fx'.
      apply HF' in Fx'.
      take (Forall _ Fs) and apply Forall_forall with (x:=F') in it; auto.
      apply PS_disjoint1 with (2:=Fx) in it; auto.
    Qed.

    Lemma check_disjoint_fresh_correct:
      forall e F,
        check_disjoint_fresh e = Some F ->
        DisjointFresh (idck (Env.elements venv)) e
        /\ (forall x, Is_fresh_in x e <-> PS.In x F).
    Proof.
      assert (forall es1 es2 fs1 fs2,
                 Forall2 (fun e F => forall x, Is_fresh_in x e <-> PS.In x F) es1 fs1 ->
                 Forall2 (fun e F => forall x, Is_fresh_in x e <-> PS.In x F) es2 fs2 ->
                 Forall (fun t => PS.Empty (PS.inter (PSUnion fs1) t)) fs2 ->
                 Forall (fun e => forall x, Is_fresh_in x e -> ~ Exists (Is_fresh_in x) es2) es1)
        as L1.
      { induction es1 as [|e es1 IH]; auto.
        intros es2 fs1 fs2 FA1 FA2 DJ. inversion FA1 as [|???? FI FA]; subst.
        constructor.
        - intros x Fx. apply FI in Fx.
          apply Forall2_ignore2 in FA2.
          apply Forall_Exists_neg, Forall_impl_In with (2:=FA2).
          intros e' Ie' (s & Is & FI') Fx'.
          apply FI' in Fx'. rewrite Forall_forall in DJ. apply DJ in Is.
          apply (Is x). rewrite PS.inter_spec, PSUnion_cons.
          auto using PSF.union_2.
        - eapply IH; eauto. apply Forall_impl_In with (2:=DJ).
          intros f If Df x Ix. apply (Df x).
          apply PS.inter_spec in Ix as (Ix1 & Ix2).
          apply PS.inter_spec. split; auto.
          rewrite PSUnion_cons. auto using PSF.union_3. }
      assert (forall es ss,
                 Forall2 (fun e s => check_disjoint_fresh e = Some s) es ss ->
                 Forall (fun e => forall F, check_disjoint_fresh e = Some F ->
                                    DisjointFresh (idck (Env.elements venv)) e
                                    /\ (forall x, Is_fresh_in x e <-> PS.In x F)) es ->
                 Forall (DisjointFresh (idck (Env.elements venv))) es
                 /\ Forall2 (fun e F => forall x, Is_fresh_in x e <-> PS.In x F) es ss) as L2.
      { intros es ss FA2 FA. split.
        - apply Forall2_ignore2 in FA2.
          apply Forall_impl_In with (2:=FA2).
          intros e Ie (? & Ix & CDF).
          rewrite Forall_forall in FA.
          apply FA with (1:=Ie) in CDF as (? & ?); auto.
        - apply Forall2_impl_In with (2:=FA2).
          intros e E Ie IE CDF. rewrite Forall_forall in FA.
          apply FA with (1:=Ie) in CDF as (? & ?); auto. }
      assert (forall es ss x t,
                 Forall2 (fun e F => forall x, Is_fresh_in x e <-> PS.In x F) es ss ->
                 Forall (fun s => PS.Empty (PS.inter t s)) ss ->
                 PS.In x t ->
                 Forall (fun e => ~Is_fresh_in x e) es) as L3.
      { intros es ss x t FA2 FA Ix.
        apply Forall2_ignore2 in FA2. apply Forall_impl_In with (2:=FA2).
        intros e' Ie' (s & Is & Ps) Fs. apply Ps in Fs.
        apply Forall_forall with (2:=Is) in FA. apply (FA x).
        auto using PSF.inter_3. }
      assert (forall es ss x F Fs,
                 Forall2 (fun e F => forall x : ident, Is_fresh_in x e <-> PS.In x F) es ss ->
                 Forall (fun s => PS.Empty (PS.inter (PSUnion (F :: Fs)) s)) ss ->
                 PS.In x F ->
                 Forall (fun e => ~ Is_fresh_in x e) es) as L4.
      { intros es ss x F Fx FA2 FA Ix.
        apply Forall2_ignore2 in FA2. apply Forall_impl_In with (2:=FA2).
        intros e' Ie' (s & Is & Ps) Fe'. apply Ps in Fe'.
        apply Forall_forall with (2:=Is) in FA. apply (FA x).
        rewrite PSUnion_cons. auto using PSF.inter_3, PSF.union_2. }
      assert (forall x xs ss,
                 Forall (fun s => PS.Empty (PS.inter (PSUnion (x :: xs)) s)) ss ->
                 Forall (fun s => PS.Empty (PS.inter (PSUnion xs) s)) ss) as L5.
      { intros x xs ss FA. apply Forall_impl_In with (2:=FA).
        intros s Is EI. intro z. specialize (EI z). intro Iz.
        apply PS.inter_spec in Iz as (? & ?).
        apply EI, PS.inter_spec. rewrite PSUnion_cons. auto using PSF.union_3. }

      Local Hint Resolve <-Exists_app'.
      Local Hint Resolve <-Exists_exists.
      Local Hint Resolve ->Forall_Exists_neg.
      Local Hint Resolve <-DisjointFreshList_app.
      Local Hint Constructors DisjointFresh.
      Local Hint Constructors DisjointFreshList.
      Local Hint Constructors Is_fresh_in.
      Local Hint Resolve Disjoint_Is_fresh_in_DisjointFreshList.
      Local Hint Resolve Forall_app.
      Local Hint Resolve In_In_PSUnion.

      induction e using exp_ind2; simpl; intros F CD; split;
        repeat match goal with
               | ro:option exp |- _ => destruct ro
               | H:Some _ = Some _ |- _ => inv H
               | H:_ \/ _ |- _ => destruct H; subst
               | H:context [ PSUnion (PS.empty :: _) ] |- _ =>
                 rewrite PSUnion_cons_empty in H
               | |- context [ PSUnion (_ :: _) ] => rewrite PSUnion_cons
               | |- context [ PS.In _ (PS.union _ _) ] => rewrite PS.union_spec
               | |- (forall x, _ <-> _) => intro; split; [inversion_clear 1|intro HH]
               | H:PS.In ?x PS.empty |- _ => inv H
               | H:check_disjoint_fresh ?e = Some ?F,
                 IH:(forall F : PS.t, check_disjoint_fresh ?e = Some F -> _) |- _
                 => apply IH in H as (? & ?)
               | H:(forall x, Is_fresh_in x ?e <-> PS.In x ?s) |- _ =>
                 assert (forall x, Is_fresh_in x e -> PS.In x s) by (setoid_rewrite H; auto);
                   assert (forall x, PS.In x s -> Is_fresh_in x e) by (setoid_rewrite <-H; auto);
                   clear H
               | H:obind ?v _ = Some _ |- _ =>
                 let OE:=fresh "OE0" in destruct v eqn:OE; [simpl in H|now omonadInv H]
               | H:forall F, Some _ = Some _ -> _ |- _ => specialize (H _ eq_refl) as (? & ?)
               | H:assert_no_intersection _ _ = Some _ |- _ =>
                 apply assert_no_intersection_correct in H as (? & ?); subst
               | E:PS.Empty (PS.inter _ _) |- _ =>
                 pose proof (PS_disjoint1 _ _ E); pose proof (PS_disjoint2 _ _ E); clear E
               | |- PS.In _ (PS.union _ _) => apply PS.union_spec
               | H:PS.In ?x (PS.union _ _) |- _ => apply PSF.union_1 in H
               | H: Exists _ (_ ++ _) |- _ => apply Exists_app' in H
               | H:ofold_right _ (ofold_right assert_no_intersection ?F ?xs) _ = Some F |- _ =>
                 let OFR:=fresh "OFR" in destruct (ofold_right assert_no_intersection F xs) eqn:OFR
               | H:ofold_right assert_no_intersection _ _ = Some _ |- _ =>
                 apply ofold_right_assert_no_intersection in H as (? & ?)
               | H:ofold_right _ None _ = Some _ |- _ =>
                 now rewrite ofold_right_none_none in H
               | H:Forall2 (fun e s => check_disjoint_fresh e = Some s) _ _ |- _ =>
                 apply L2 in H as (? & ?); [|now auto]
               | H:Exists (Is_fresh_in _) _ |- _ => apply Exists_exists in H as (? & ? & ?)
               | H:omap check_disjoint_fresh _ = Some _ |- _ => apply omap_inversion in H
               | H:ofold_right assert_no_intersection (check_disjoint_fresh ?e) ?xs = Some ?s |- _ =>
                 let CDF:=fresh "CDF" in destruct (check_disjoint_fresh e) eqn:CDF
               | H:ofold_right check_anon_name _ _ = Some _ |- _ =>
                 apply ofold_right_check_anon_name_correct in H as (? & ? & ? & ?)
               | H:DisjointSetList (_ :: _) |- _ => inv H
               | T:?t === PSUnion _, H:context [PS.inter ?t _] |- _ =>
                 setoid_rewrite T in H
               | EQ:?F === PSUnion ?xs |- PS.In _ ?F => rewrite EQ
               | EQ:?F === PSUnion ?xs, H:PS.In _ ?F |- _ => rewrite EQ in H
               | E:?t === PSUnion ?xs |- context [ PS.In _ ?t ] => rewrite E
               | E:?F === PSUnion (_ :: _), FI:PS.In ?x ?F |- _ => rewrite E in FI
               | E:?t === PSUnion ?xs, FI:PS.In ?x (PSUnion (?t::?ys)) |- _ =>
                 let RR:=fresh "RR" in
                 assert (SetoidList.eqlistA PS.Equal (t :: ys) (PSUnion xs :: ys)) as RR
                     by (constructor; intuition);
                   rewrite RR, PSUnion_app, PSUnion_In_app in FI; clear RR
               | FA:Forall2 (fun e F => forall x, Is_fresh_in x e <-> PS.In x F) ?es ?xs,
                    Ix:In ?x ?es |- _ =>
                 apply Forall2_ignore2, Forall_forall with (2:=Ix) in FA as (? & ? & ?)
               | FA:Forall2 (fun e F => forall x, Is_fresh_in x e <-> PS.In x F) ?es ?Fs,
                    Ix:In ?x ?Fs |- _ =>
                 apply Forall2_ignore1, Forall_forall with (2:=Ix) in FA as (? & ? & ?)
               | H:PS.In ?x (PSUnion ?xs) |- _ =>
                 apply PSUnion_In_In in H as (? & ? & ?)
               | H:In ?x (_ :: _) |- _ => apply in_inv in H
               | H:In _ (_ ++ _) |- _ => apply in_app in H
               | FP:(forall x, Is_fresh_in x ?e -> PS.In x ?s), FI:Is_fresh_in ?x ?e |- PS.In ?x ?F =>
                 apply FP in FI
               | Ix:Ino ?x (map stream_name ?anns),
                 H:(forall x, Ino x (map stream_name ?anns) <-> _ /\ _) |- _
                 => apply H in Ix as (? & ?); auto
               | SS:PS.Subset ?t ?F, TE:?t === PSUnion _ |- PS.In ?x ?F =>
                 rewrite <-SS, TE, ?PSUnion_cons, ?PS.union_spec; auto
               end;
        eauto 20.
      - (* DisjointFresh (idck (Env.elements venv)) (Ebinop op e1 e2 a) *)
        constructor; firstorder.
      - (* DisjointFresh (idck (Env.elements venv)) (Eapp f es (Some e) a) *)
        constructor; eauto 6.
        intros x Ix.
        take (forall x, Ino x (map stream_name _) <-> _ /\ _) and apply it in Ix as (Nx & Ix).
        take (_ === PSUnion (_ :: _)) and rewrite it, PSUnion_cons, PS.union_spec, not_or' in Nx.
        destruct Nx as (? & ?).
        apply Forall_Exists_neg; constructor; auto.
        take (Forall2 _ _ _) and apply Forall2_ignore2 in it.
        apply Forall_impl_In with (2:=it).
        intros e' Ie' (z & Iz & Pz) Fe'.
        apply Pz in Fe'; eauto.
      - (* DisjointFresh (idck (Env.elements venv)) (Eapp f es None a) *)
        constructor; eauto.
        intros x Ix.
        take (forall x, Ino x (map stream_name _) <-> _ /\ _) and apply it in Ix as (Nx & Ix).
        take (_ === PSUnion _) and rewrite it in Nx.
        apply Forall_Exists_neg.
        take (Forall2 _ _ _) and apply Forall2_ignore2 in it.
        apply Forall_impl_In with (2:=it).
        intros e' Ie' (z & Iz & Pz) Fe'.
        apply Pz in Fe'; eauto.
      - (* Is_fresh_in x (Eapp f es (Some e) a) *)
        constructor.
        destruct (PSP.In_dec x t) as [Ix|Nx].
        + left.
          take (t === PSUnion _) and rewrite it, PSUnion_cons, PS.union_spec in Ix.
          destruct Ix as [Ix|Ix]; auto.
          apply PSUnion_In_In in Ix as (? & Ix1 & Ix2).
          take (Forall2 _ _ _) and apply Forall2_ignore1, Forall_forall
            with (2:=Ix1) in it as (? & ? & IFI).
          apply IFI in Ix2; eauto.
        + right; firstorder.
      - (* Is_fresh_in x (Eapp f es None a) *)
        constructor.
        destruct (PSP.In_dec x t) as [Ix|Nx].
        + left.
          take (t === _) and rewrite it in Ix.
          apply PSUnion_In_In in Ix as (? & Ix1 & Ix2).
          take (Forall2 _ _ _) and apply Forall2_ignore1 in it;
            apply Forall_forall with (2:=Ix1) in it as (? & ? & IFI);
            apply IFI in Ix2; eauto.
        + right. firstorder.
    Qed.

    Lemma check_wellformedanon_correct:
      forall e,
        check_wellformedanon e = true ->
        WellFormedAnon (idck (Env.elements venv)) e.
    Proof.
      intros e CW.
      destruct e; simpl in *;
        try apply isSome_true in CW as (? & ?);
        eauto using (proj1 (check_disjoint_fresh_correct _ _ _)).
      DestructMatch.
      apply isSome_true in CW as (F & CW).
      match goal with H:omap check_disjoint_fresh ?ls = Some ?ys |- _ =>
        rename ls into es, ys into Fs, H into CDF end.
      apply omap_inversion in CDF.
      assert (Forall (DisjointFresh (idck (Env.elements venv))) es) as DF.
      { apply Forall2_ignore2 in CDF. apply Forall_impl_In with (2:=CDF).
        intros e Ie (F' & IF' & CDF').
        apply check_disjoint_fresh_correct in CDF' as (? & ?); eauto. }
      assert (Forall2 (fun e F => forall x, Is_fresh_in x e <-> PS.In x F) es Fs) as FI.
      { apply Forall2_impl_In with (2:=CDF).
        intros e s Ie Is CDF'.
        apply check_disjoint_fresh_correct in CDF' as (? & ?); eauto. }
      take (option exp) and destruct it.
      - destruct (check_disjoint_fresh e) eqn:CDFe;
          [|now rewrite ofold_right_none_none in CW].
        apply ofold_right_assert_no_intersection in CW as (HF & DL).
        apply check_disjoint_fresh_correct in CDFe as (DFe & FIe).
        eauto using Disjoint_Is_fresh_in_DisjointFreshList.
      - apply ofold_right_assert_no_intersection in CW as (HF & DL).
        inv DL. eauto using Disjoint_Is_fresh_in_DisjointFreshList.
    Qed.

    Lemma check_var_correct:
      forall x ck,
        check_var x ck = true <-> In (x, ck) (idck (Env.elements venv)).
    Proof.
      unfold check_var. split; intros HH.
      - DestructMatch; simpl.
        rewrite equiv_decb_equiv in HH. inv HH.
        take (Env.find _ _ = Some _) and apply Env.elements_correct in it; eauto.
      - apply In_idck_exists in HH as (ty & HH).
        apply Env.elements_complete in HH as ->.
        apply equiv_decb_refl.
    Qed.

    Lemma check_paired_clocks_correct:
      forall cks1 cks2 anns,
        forall3b check_paired_clocks cks1 cks2 anns = true ->
        map stripname cks1 = map clock_of_nclock anns
        /\ map stripname cks2 = map clock_of_nclock anns
        /\ Forall unnamed_stream anns.
    Proof.
      unfold unnamed_stream.
      setoid_rewrite forall3b_Forall3.
      induction 1 as [|(ck1, n1) (ck2, n2) (ty, (ck, n)) cks1 cks2 anns
                                 IH1 IH2 (Hcks1 & Hcks2 & Hanns)];
        subst; simpl in *; eauto.
      destruct n; try discriminate.
      rewrite Bool.andb_true_iff in IH1.
      setoid_rewrite equiv_decb_equiv in IH1.
      destruct IH1 as (Hck1 & Hck2). inv Hck1; inv Hck2.
      rewrite Hcks1, Hcks2; auto.
    Qed.

    Lemma check_merge_clocks_correct:
      forall {A} x ck nc1 nc2 (ty : A),
        check_merge_clocks x ck nc1 nc2 ty = true ->
        stripname nc1 = Con ck x true
        /\ stripname nc2 = Con ck x false.
    Proof.
      intros A x ck (ck1, n1) (ck2, n2) ty CM; simpl in CM.
      DestructMatch; subst.
      repeat rewrite Bool.andb_true_iff in CM.
      repeat take (_ /\ _) and destruct it.
      now repeat take (_ ==b _ = true) and rewrite equiv_decb_equiv in it; inv it.
    Qed.

    Lemma check_forall3b_merge_clocks_correct:
      forall {A} x ck ets efs (tys : list A),
        forall3b (check_merge_clocks x ck) (nclocksof ets) (nclocksof efs) tys = true ->
        Forall (eq (Con ck x true)) (clocksof ets)
        /\ Forall (eq (Con ck x false)) (clocksof efs)
        /\ length (clocksof ets) = length tys
        /\ length (clocksof efs) = length tys.
    Proof.
      setoid_rewrite forall3b_Forall3.
      intros * FA3. pose proof (Forall3_length _ _ _ _ FA3) as (L1 & L2).
      setoid_rewrite clocksof_nclocksof; setoid_rewrite Forall_map.
      setoid_rewrite map_length. rewrite L2, L1, L2.
      repeat split; auto.
      - apply Forall3_ignore23 in FA3.
        apply Forall_impl_In with (2:=FA3).
        intros nc Inc (y & z & CE).
        now apply check_merge_clocks_correct in CE as (? & ?).
      - apply Forall3_ignore13 in FA3.
        apply Forall_impl_In with (2:=FA3).
        intros nc Inc (y & z & CE).
        now apply check_merge_clocks_correct in CE as (? & ?).
    Qed.

    Lemma check_ite_clocks_correct:
      forall {A} ck nc1 nc2 (ty : A),
        check_ite_clocks ck nc1 nc2 ty = true ->
        stripname nc1 = ck
        /\ stripname nc2 = ck.
    Proof.
      intros A ck (ck1, n1) (ck2, n2) ty CM.
      unfold check_ite_clocks in CM.
      rewrite Bool.andb_true_iff in CM.
      take (_ /\ _) and destruct it.
      now repeat take (_ ==b _ = true) and rewrite equiv_decb_equiv in it; inv it.
    Qed.

    Lemma check_forall3b_ite_clocks_correct:
      forall {A} ck ncs1 ncs2 (tys : list A),
        forall3b (check_ite_clocks ck) (nclocksof ncs1) (nclocksof ncs2) tys = true ->
        length (clocksof ncs1) = length tys
        /\ length (clocksof ncs2) = length tys
        /\ Forall (eq ck) (clocksof ncs1)
        /\ Forall (eq ck) (clocksof ncs2).
    Proof.
      setoid_rewrite forall3b_Forall3.
      intros * FA3. pose proof (Forall3_length _ _ _ _ FA3) as (L1 & L2).
      setoid_rewrite clocksof_nclocksof; setoid_rewrite Forall_map.
      setoid_rewrite map_length. rewrite L2, L1, L2.
      repeat split; auto.
      - apply Forall3_ignore23 in FA3.
        apply Forall_impl_In with (2:=FA3).
        intros nc Inc (y & z & CE).
        now apply check_ite_clocks_correct in CE as (? & ?).
      - apply Forall3_ignore13 in FA3.
        apply Forall_impl_In with (2:=FA3).
        intros nc Inc (y & z & CE).
        now apply check_ite_clocks_correct in CE as (? & ?).
    Qed.

    Lemma oconcat_map_check_exp':
      forall {f} es cks,
        (forall e cks,
            In e es ->
            f e = Some cks ->
            wc_exp G (idck (Env.elements venv)) e /\ nclockof e = cks) ->
        oconcat (map f es) = Some cks ->
        Forall (wc_exp G (idck (Env.elements venv))) es
        /\ nclocksof es = cks.
    Proof.
      induction es as [|e es IH]; intros cks WTf CE. now inv CE; auto.
      simpl in CE. destruct (f e) eqn:Ce; [|now omonadInv CE].
      destruct (oconcat (map f es)) as [ces|]; [|now omonadInv CE].
      omonadInv CE. simpl.
      apply WTf in Ce as (Ce1 & ->); auto with datatypes.
      destruct (IH ces) as (? & ->); auto.
      intros * Ies Fe. apply WTf in Fe; auto with datatypes.
    Qed.

    Lemma find_add_isub:
      forall sub x tc ck nm,
        ~Env.In x sub ->
        Env.find x (add_isub sub (x, tc) (ck, nm)) = nm.
    Proof.
      unfold add_isub; simpl. intros sub x (ty, ck) ? nm NI.
      destruct nm. now rewrite Env.gss.
      now apply Env.Props.P.F.not_find_in_iff in NI.
    Qed.

    Lemma fold_left2_add_osub_skip:
      forall x xs anns sub,
        ~In x (map fst xs) ->
        Env.find x (fold_left2 add_osub xs anns sub) = Env.find x sub.
    Proof.
      induction xs as [|(y, (yt, yc)) xs IH]; auto.
      simpl; intros anns sub NIx.
      apply Decidable.not_or in NIx as (Nx & NIx).
      destruct anns as [|(ty, (ck, n)) anns]; auto.
      rewrite (IH _ _ NIx).
      unfold add_osub, add_isub; simpl.
      destruct n; auto.
      rewrite Env.gso; auto.
    Qed.

    Lemma fold_left2_add_isub_skip:
      forall x xs ncs sub,
        ~In x (map fst xs) ->
        Env.find x (fold_left2 add_isub xs ncs sub) = Env.find x sub.
    Proof.
      induction xs as [|(y, (yt, yc)) xs IH]; auto.
      simpl; intros ncs sub NIx.
      apply Decidable.not_or in NIx as (Nx & NIx).
      destruct ncs as [|(ck, n) anns]; auto.
      rewrite (IH _ _ NIx).
      unfold add_isub; simpl.
      destruct n; auto.
      rewrite Env.gso; auto.
    Qed.

    Lemma fold_left2_add_isub:
      forall x xt xc ck nm xs ncs sub,
        In ((x, (xt, xc)), (ck, nm)) (combine xs ncs) ->
        NoDupMembers xs ->
        ~Env.In x sub ->
        Env.find x (fold_left2 add_isub xs ncs sub) = nm.
    Proof.
      induction xs as [|(y, (yt, yc)) xs IH]. now inversion 1.
      intros ncs sub Ix ND NI.
      destruct ncs as [|(ck', nm') ncs]. now inversion Ix.
      simpl in *.
      destruct Ix as [Ix|Ix].
      - inv Ix. inv ND. rewrite fold_left2_add_isub_skip.
        now apply find_add_isub.
        rewrite in_map_iff.
        intros ((y, (yt, yc)) & Fy & Iy). simpl in *; subst.
        take (~InMembers _ _) and apply it.
        apply In_InMembers with (1:=Iy).
      - inv ND. eapply IH in Ix; eauto.
        apply in_combine_l, In_InMembers in Ix.
        take (~InMembers _ xs) and apply InMembers_neq with (2:=it) in Ix.
        unfold add_isub; simpl. destruct nm'; auto.
        setoid_rewrite Env.Props.P.F.add_in_iff.
        apply not_or'; auto.
    Qed.

    Lemma fold_left2_add_osub:
      forall x xt xc ty ck nm xs ans sub,
        In ((x, (xt, xc)), (ty, (ck, nm))) (combine xs ans) ->
        NoDupMembers xs ->
        ~Env.In x sub ->
        Env.find x (fold_left2 add_osub xs ans sub) = nm.
    Proof.
      induction xs as [|(y, (yt, yc)) xs IH]. now inversion 1.
      intros ncs sub Ix ND NI.
      destruct ncs as [|(ck', nm') ncs]. now inversion Ix.
      simpl in *.
      destruct Ix as [Ix|Ix].
      - inv Ix. inv ND. rewrite fold_left2_add_osub_skip.
        now apply find_add_isub.
        rewrite in_map_iff.
        intros ((y, (yt, yc)) & Fy & Iy). simpl in *; subst.
        take (~InMembers _ _) and apply it.
        apply In_InMembers with (1:=Iy).
      - inv ND. eapply IH in Ix; eauto.
        apply in_combine_l, In_InMembers in Ix.
        take (~InMembers _ xs) and apply InMembers_neq with (2:=it) in Ix.
        unfold add_osub, add_isub; simpl. destruct nm'; auto. simpl.
        destruct o; auto.
        setoid_rewrite Env.Props.P.F.add_in_iff.
        apply not_or'; auto.
    Qed.

    Lemma check_inst_correct:
      forall bck xc ck sub,
        check_inst bck sub xc ck = true ->
        instck bck (fun x => Env.find x sub) xc = Some ck.
    Proof.
      induction xc as [|xc' ? x b]; simpl.
      now setoid_rewrite equiv_decb_equiv; inversion 2.
      destruct ck. now inversion 1.
      intros sub Fx. DestructMatch.
      repeat take (_ && _ = true) and apply andb_prop in it as (? & ?).
      repeat take ((_ ==b _) = true) and rewrite equiv_decb_equiv in it; inv it.
      now take (check_inst _ _ _ _ = true) and apply IHxc in it as ->.
    Qed.

    Lemma check_exp_correct:
      forall e ncks,
        check_exp e = Some ncks ->
        wc_exp G (idck (Env.elements venv)) e
        /\ nclockof e = ncks.
    Proof.
      induction e using exp_ind2; simpl; intros ncks CE;
      repeat progress
               match goal with
               | H:None = Some _ |- _ => discriminate
               | H:Some _ = Some _ |- _ => inv H
               | a:ann |- _ => destruct a
               | a:lann |- _ => destruct a
               | nc:nclock |- _ => destruct nc
               | H:obind _ _ = Some _ |- _ => omonadInv H
               | H: _ && _ = true |- _ => apply Bool.andb_true_iff in H as (? & ?)
               | H: ((_ ==b _) = true) |- _ => rewrite equiv_decb_equiv in H; inv H
               | H:(if ?c then Some _ else None) = Some _ |- _ =>
                 let C := fresh "C0" in
                 destruct c eqn:C
               | H:check_var _ _ = true |- _ => apply check_var_correct in H
               | H:assert_singleton _ = Some _ |- _ => apply assert_singleton_spec in H
               | H:obind ?v _ = Some _ |- _ =>
                 let OE:=fresh "OE0" in destruct v eqn:OE; [simpl in H|now omonadInv H]
               | H:(match ?o with Some _ => _ | None => None end) = Some _ |- _ =>
                 destruct o
               | H:(match ?o with Some _ => None | None => _ end) = Some _ |- _ =>
                 destruct o
               | H:(match ?c with Cbase => None | _ => _ end) = Some _ |- _ =>
                 destruct c
               | H:forall3b check_paired_clocks ?cks1 ?cks2 ?anns = true |- _ =>
                 apply check_paired_clocks_correct in H as (? & ? & ?)
               | H:(?xs <>b 0) = true |- _ =>
                 apply nequiv_decb_true in H;
                   assert (0 < xs) by (destruct l;
                     [now exfalso; apply H|apply PeanoNat.Nat.lt_0_succ])
               | H:obind2 (assert_singleton ?ce) _ = Some _ |- _ =>
                 destruct (assert_singleton ce) as [(ck, n)|] eqn:AS;
                   try discriminate; simpl in H
               end.
      - (* Econst *)
        eauto using wc_exp.
      - (* Evar *)
        eauto using wc_exp.
      - (* Eunop *)
        apply IHe in OE0 as (? & ?).
        eauto using wc_exp, nclockof_clockof.
      - (* Ebinop *)
        apply IHe1 in OE0 as (? & ?); apply IHe2 in OE1 as (? & ?).
        eauto using wc_exp, nclockof_clockof.
      - (* Efby *)
        repeat take (Forall (fun e :exp => _) _) and rewrite Forall_forall in it.
        apply oconcat_map_check_exp' in OE0 as (? & ?); auto.
        apply oconcat_map_check_exp' in OE1 as (? & ?); auto. subst.
        repeat take (map stripname _ = map clock_of_nclock _)
               and rewrite <-clocksof_nclocksof in it.
        eauto using wc_exp.
      - (* Ewhen *)
        take (Forall _ es) and rewrite Forall_forall in it.
        take (oconcat (map check_exp _) = Some _) and
             apply oconcat_map_check_exp' in it as (? & ?); auto.
        take (forall2b _ _ _ = true) and rename it into FA2; apply forall2b_Forall2 in FA2.
        subst; simpl; repeat split; auto. constructor; auto; rewrite clocksof_nclocksof.
        2:rewrite map_length; pose proof (Forall2_length _ _ _ FA2) as Hlen; auto.
        apply Forall2_ignore2 in FA2. rewrite Forall_map.
        apply Forall_impl_In with (2:=FA2). intros (? & ?) ? (? & HH).
        now rewrite equiv_decb_equiv in HH; inv HH.
      - (* Emerge *)
        repeat take (Forall _ _) and rewrite Forall_forall in it.
        repeat take (oconcat (map check_exp _) = Some _) and
               apply oconcat_map_check_exp' in it as (? & ?); auto.
        repeat take (nclocksof _ = _) and rewrite <- it in *; clear it.
        take (forall3b (check_merge_clocks _ _) _ _ _ = true)
        and apply check_forall3b_merge_clocks_correct in it as (? & ? & ? & ?).
        eauto using wc_exp.
      - (* Eite *)
        repeat take (Forall _ _) and rewrite Forall_forall in it.
        repeat take (oconcat (map check_exp _) = Some _) and
               apply oconcat_map_check_exp' in it as (? & ?); auto.
        repeat take (nclocksof _ = _) and rewrite <- it in *; clear it.
        take (forall3b (check_ite_clocks _) _ _ _ = true)
        and apply check_forall3b_ite_clocks_correct in it as (? & ? & ? & ?).
        apply IHe in AS as (? & ?); auto.
        eauto using wc_exp, nclockof_clockof.
      - (* Eapp *)
        take (Forall _ _) and rewrite Forall_forall in it.
        take (oconcat (map check_exp _) = Some _) and
             apply oconcat_map_check_exp' in it as (? & ?); auto.
        take (nclocksof _ = _) and rewrite <- it in *; clear it.
        repeat take (forall2b _ _ _ = true) and apply forall2b_Forall2 in it.
        split; auto.
        match goal with H:find_base_clock _ _ = Some ?c |- _ => rename c into bck end.

        assert (Forall2 (WellInstantiated bck
           (fun x => Env.find x (fold_left2 add_osub n.(n_out) a
              (fold_left2 add_isub n.(n_in) (nclocksof es) (Env.empty _)))))
                        (idck n.(n_in)) (nclocksof es)).
        { apply Forall2_map_1, Forall2_forall.
          take (Forall2 _ n.(n_in) (nclocksof es)) and rename it into FA2.
          split; [|now apply Forall2_length with (1:=FA2)].
          intros (x, (xt, xc)) (ck, nm) Ix.
          constructor; simpl;
            [|now apply Forall2_In with (1:=Ix), check_inst_correct in FA2].
          pose proof (NoDupMembers_app_l _ _ n.(n_nodup)).
          rewrite fold_left2_add_osub_skip, fold_left2_add_isub with (1:=Ix); auto.
          now rewrite Env.Props.P.F.empty_in_iff.
          apply in_combine_l, In_InMembers in Ix.
          rewrite <-fst_InMembers.
          apply NoDupMembers_app_InMembers with (2:=Ix).
          pose proof n.(n_nodup) as ND.
          now rewrite Permutation_swap in ND; apply NoDupMembers_app_r in ND. }

        assert (Forall2 (WellInstantiated bck
           (fun x => Env.find x (fold_left2 add_osub n.(n_out) a
             (fold_left2 add_isub n.(n_in) (nclocksof es) (Env.empty ident)))))
                        (idck n.(n_out)) (map snd a)).
        { apply Forall2_map_1, Forall2_forall.
          take (Forall2 _ n.(n_out) _) and rename it into FA2.
          split; [|now rewrite map_length; apply Forall2_length with (1:=FA2)].
          intros (x, (xt, xc)) (ck, nm) Ix.
          rewrite combine_map_snd, in_map_iff in Ix.
          destruct Ix as (((y & (yt & yc)), (yc' & ynm)) & EE & Ix); inv EE.
          constructor; simpl.
          2:now apply Forall2_In with (1:=Ix), check_inst_correct in FA2.
          pose proof (NoDupMembers_app_r _ _ (NoDupMembers_app_r _ _ n.(n_nodup))).
          rewrite fold_left2_add_osub with (1:=Ix); auto.
          setoid_rewrite Env.Props.P.F.not_find_in_iff.
          rewrite fold_left2_add_isub_skip; auto using Env.gempty.
          rewrite <-fst_InMembers.
          apply in_combine_l, In_InMembers in Ix.
          apply NoDupMembers_app_InMembers with (2:=Ix).
          rewrite Permutation_app_comm.
          pose proof n.(n_nodup) as ND.
          now rewrite Permutation_swap in ND; apply NoDupMembers_app_r in ND. }
        destruct ro;
          simpl in *; DestructMatch; subst;
            try match goal with H:check_exp ?e = Some [?nc] |- _ => destruct nc end;
            econstructor; eauto;
            take (forall ncks, Some _ = Some ncks -> _ /\ _) and rename it into CE;
            specialize (CE _ eq_refl) as (CE1 & CE2); eauto.
        now apply nclockof_clockof with (1:=CE2).
    Qed.

    Lemma oconcat_map_check_wellformedanon_and_exp:
      forall es ncks,
        oconcat (map check_wellformedanon_and_exp es) = Some ncks ->
        Forall (wc_exp G (idck (Env.elements venv))) es
        /\ nclocksof es = ncks
        /\ Forall (WellFormedAnon (idck (Env.elements venv))) es.
    Proof.
      induction es as [|e es IH]; intros ncks CE. now inv CE; eauto.
      simpl in CE. DestructMatch.
      take (check_wellformedanon_and_exp _ = Some _) and rename it into CWF.
      unfold check_wellformedanon_and_exp in CWF.
      DestructMatch.
      take (check_wellformedanon _ = true)
           and apply check_wellformedanon_correct in it.
      apply check_exp_correct in CWF as (WCe & NCe).
      destruct (oconcat (map check_wellformedanon_and_exp es)) eqn:CWF; inv CE.
      specialize (IH _ eq_refl) as (? & ? & ?).
      simpl. take (nclocksof _ = _) and rewrite it. eauto.
    Qed.

    Lemma check_equation_correct:
      forall eq,
        check_equation eq = true ->
        wc_equation G (idck (Env.elements venv)) eq.
    Proof.
      intros eq CE. destruct eq as (xs, es); simpl in CE.
      DestructMatch.
      take (oconcat (map _ _) = Some _)
      and apply oconcat_map_check_wellformedanon_and_exp in it as (WC & NC & WA).
      subst. apply forall2b_Forall2 in CE.
      constructor; auto.
      rewrite clocksof_nclocksof, Forall2_map_2.
      split; auto.
      split; apply Forall2_impl_In with (2:=CE); intros x (ck, nm) Ix Inc CNC;
        simpl in *; DestructMatch;
        apply Bool.andb_true_iff in CNC as (CNC1 & CNC2);
        take (check_var _ _ = true) and apply check_var_correct in it;
        auto.
      destruct nm; simpl; auto.
      now rewrite equiv_decb_equiv in CNC2.
    Qed.

  End ValidateExpression.

End LCLOCKING.

Module LClockingFun
       (Ids  : IDS)
       (Op   : OPERATORS)
       (Syn  : LSYNTAX Ids Op)
       <: LCLOCKING Ids Op Syn.
  Include LCLOCKING Ids Op Syn.
End LClockingFun.
