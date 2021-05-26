From Velus Require Import Common.
From Velus Require Import CommonProgram.
From Velus Require Import CommonTyping.
From Velus Require Import Environment.
From Velus Require Import Operators.
From Velus Require Import Clocks.
From Velus Require Import Lustre.LSyntax.

From Coq Require Import List.
Import List.ListNotations.
Open Scope list_scope.

From Coq Require Import Morphisms.
From Coq Require Import Permutation.

From Coq Require Import Program.Basics Program.Wf.
Open Scope program_scope.

(** * Lustre clocking *)

(**

  Clocking judgements for Lustre.
  Classify Lustre programs which are statically well-formed.

 *)

Module Type LCLOCKING
       (Import Ids   : IDS)
       (Import Op    : OPERATORS)
       (Import OpAux : OPERATORS_AUX Ids Op)
       (Import Cks   : CLOCKS Ids Op OpAux)
       (Import Syn   : LSYNTAX Ids Op OpAux Cks).

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

       To treat this detail, we introduce "named streams" that allow us to
       bind such flows to a local name. Clock annotations within
       expressions are then made with "named clocks" (nclock), a pair where
       the second member is either None for an anonymous stream, or Some for
       a locally named stream.

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
       of clocks is ensured by a constraint (NoDup) applied on the collected
       clocks (anon_in).

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

    Context {prefs : PS.t}.

    Variable G    : @global prefs.
    Variable vars : list (ident * clock).

    (** EvarAnon is used at toplevel of an equation, to allow for equations of the form
        x = y, without having to specify a name. Evar is used internally to expressions *)
    Inductive wc_exp : exp -> Prop :=
    | wc_Econst: forall c,
        wc_exp (Econst c)

    | wc_Eenum: forall x ty,
        wc_exp (Eenum x ty)

    | wc_Evar: forall x ty ck,
        In (x, ck) vars ->
        wc_exp (Evar x (ty, (ck, Some x)))

    | wc_EvarAnon: forall x ty ck,
        In (x, ck) vars ->
        wc_exp (Evar x (ty, (ck, None)))

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

    | wc_Efby: forall e0s es er anns,
        Forall wc_exp e0s ->
        Forall wc_exp es ->
        Forall wc_exp er ->
        Forall2 eq (map clock_of_nclock anns) (clocksof e0s) ->
        Forall2 eq (map clock_of_nclock anns) (clocksof es) ->
        Forall (fun e => exists ck, clockof e = [ck]) er ->
        Forall unnamed_stream anns ->
        wc_exp (Efby e0s es er anns)

    | wc_Earrow: forall e0s es er anns,
        Forall wc_exp e0s ->
        Forall wc_exp es ->
        Forall wc_exp er ->
        Forall2 eq (map clock_of_nclock anns) (clocksof e0s) ->
        Forall2 eq (map clock_of_nclock anns) (clocksof es) ->
        Forall (fun e => exists ck, clockof e = [ck]) er ->
        Forall unnamed_stream anns ->
        wc_exp (Earrow e0s es er anns)

    | wc_Ewhen: forall es x ty b tys ck,
        In (x, ck) vars ->
        Forall wc_exp es ->
        Forall (eq ck) (clocksof es) ->
        length tys = length (clocksof es) ->
        wc_exp (Ewhen es x b (tys, (Con ck x (ty, b), None)))

    | wc_Emerge: forall x tx es tys ck,
        In (x, ck) vars ->
        es <> nil ->
        Forall (Forall wc_exp) es ->
        Forall2 (fun i es => Forall (eq (Con ck x (tx, i))) (clocksof es)) (seq 0 (length es)) es ->
        Forall (fun es => length tys = length (clocksof es)) es ->
        wc_exp (Emerge (x, tx) es (tys, (ck, None)))

    | wc_Ecase: forall e brs d tys ck,
        wc_exp e ->
        clockof e = [ck] ->
        brs <> nil ->
        (forall es, In (Some es) brs -> Forall wc_exp es) ->
        (forall es, In (Some es) brs -> Forall (eq ck) (clocksof es)) ->
        (forall es, In (Some es) brs -> length tys = length (clocksof es)) ->
        Forall wc_exp d ->
        Forall (eq ck) (clocksof d) ->
        length tys = length (clocksof d) ->
        wc_exp (Ecase e brs d (tys, (ck, None)))

    | wc_Eapp: forall f es er anns n bck sub,
        Forall wc_exp es ->
        Forall wc_exp er ->
        find_node f G = Some n ->
        Forall2 (WellInstantiated bck sub) (idck n.(n_in)) (nclocksof es) ->
        Forall2 (WellInstantiated bck sub) (idck n.(n_out)) (map snd anns) ->
        Forall (fun e => exists ck, clockof e = [ck]) er ->
        wc_exp (Eapp f es er anns).

  Definition wc_equation (xses : equation) : Prop :=
    let (xs, es) := xses in
    Forall wc_exp es
    /\ Forall2 (fun x nc => LiftO True (eq x) (snd nc)) xs (nclocksof es)
    /\ Forall2 (fun x ck => In (x, ck) vars) xs (clocksof es).
  End WellClocked.

  Definition wc_node {prefs : PS.t} (G: @global prefs) (n: @node prefs) : Prop
    :=    wc_env (idck  n.(n_in))
       /\ wc_env (idck (n.(n_in) ++ n.(n_out)))
       /\ wc_env (idck (n.(n_in) ++ n.(n_out) ++ n.(n_vars)))
       /\ Forall (wc_equation G (idck (n.(n_in) ++ n.(n_vars) ++ n.(n_out)))) n.(n_eqs).

  Definition wc_global {prefs} : @global prefs -> Prop :=
    wt_program wc_node.

  (** ** Basic properties of clocking *)

  Hint Constructors wc_exp : lclocking.
  Hint Unfold wc_equation wc_node wc_global wc_env : lclocking.

  Section wc_exp_ind2.
    Context (prefs : PS.t).

    Variable G    : @global prefs.
    Variable vars : list (ident * clock).
    Variable P : exp -> Prop.

    Hypothesis EconstCase:
      forall c,
        P (Econst c).

    Hypothesis EenumCase:
      forall k ty,
        P (Eenum k ty).

    Hypothesis EvarCase:
      forall x ty ck,
        In (x, ck) vars ->
        P (Evar x (ty, (ck, Some x))).

    Hypothesis EvarAnonCase:
      forall x ty ck,
        In (x, ck) vars ->
        P (Evar x (ty, (ck, None))).

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
      forall e0s es er anns,
        Forall (wc_exp G vars) e0s ->
        Forall (wc_exp G vars) es ->
        Forall (wc_exp G vars) er ->
        Forall P es ->
        Forall P e0s ->
        Forall P er ->
        Forall2 eq (map clock_of_nclock anns) (clocksof e0s) ->
        Forall2 eq (map clock_of_nclock anns) (clocksof es) ->
        Forall (fun e => exists ck, clockof e = [ck]) er ->
        Forall unnamed_stream anns ->
        P (Efby e0s es er anns).

    Hypothesis EarrowCase:
      forall e0s es er anns,
        Forall (wc_exp G vars) e0s ->
        Forall (wc_exp G vars) es ->
        Forall (wc_exp G vars) er ->
        Forall P es ->
        Forall P e0s ->
        Forall P er ->
        Forall2 eq (map clock_of_nclock anns) (clocksof e0s) ->
        Forall2 eq (map clock_of_nclock anns) (clocksof es) ->
        Forall (fun e => exists ck, clockof e = [ck]) er ->
        Forall unnamed_stream anns ->
        P (Earrow e0s es er anns).

    Hypothesis EwhenCase:
      forall es x ty b tys ck,
        In (x, ck) vars ->
        Forall (wc_exp G vars) es ->
        Forall P es ->
        Forall (eq ck) (clocksof es) ->
        length tys = length (clocksof es) ->
        P (Ewhen es x b (tys, (Con ck x (ty, b), None))).

    Hypothesis EmergeCase:
      forall x tx es tys ck,
        In (x, ck) vars ->
        es <> nil ->
        Forall (Forall (wc_exp G vars)) es ->
        Forall (Forall P) es ->
        Forall2 (fun i es => Forall (eq (Con ck x (tx, i))) (clocksof es)) (seq 0 (length es)) es ->
        Forall (fun es => length tys = length (clocksof es)) es ->
        P (Emerge (x, tx) es (tys, (ck, None))).

    Hypothesis EcaseCase:
      forall e brs d tys ck,
        wc_exp G vars e ->
        P e ->
        clockof e = [ck] ->
        brs <> nil ->
        (forall es, In (Some es) brs -> Forall (wc_exp G vars) es) ->
        (forall es, In (Some es) brs -> Forall P es) ->
        (forall es, In (Some es) brs -> Forall (eq ck) (clocksof es)) ->
        (forall es, In (Some es) brs -> length tys = length (clocksof es)) ->
        Forall (wc_exp G vars) d ->
        Forall P d ->
        Forall (eq ck) (clocksof d) ->
        length tys = length (clocksof d) ->
        P (Ecase e brs d (tys, (ck, None))).

    Hypothesis EappCase:
      forall f es er anns n bck sub,
        Forall (wc_exp G vars) es ->
        Forall (wc_exp G vars) er ->
        Forall P es ->
        Forall P er ->
        find_node f G = Some n ->
        Forall2 (WellInstantiated bck sub) (idck n.(n_in)) (nclocksof es) ->
        Forall2 (WellInstantiated bck sub) (idck n.(n_out)) (map snd anns) ->
        Forall (fun e => exists ck, clockof e = [ck]) er ->
        P (Eapp f es er anns).

    Fixpoint wc_exp_ind2 (e: exp) (H: wc_exp G vars e) {struct H} : P e.
    Proof.
      destruct H; eauto.
      - apply EfbyCase; auto.
        + clear H3. induction H0; auto.
        + clear H2. induction H; auto.
        + clear H4. induction H1; auto.
      - apply EarrowCase; auto.
        + clear H3. induction H0; auto.
        + clear H2. induction H; auto.
        + clear H4. induction H1; auto.
      - apply EwhenCase; auto.
        clear H1 H2. induction H0; auto.
      - apply EmergeCase; auto.
        clear H0 H2 H3. induction H1; constructor; auto.
        induction H0; auto.
      - apply EcaseCase; auto.
        + clear H1 H3 H4. intros ? Hin. specialize (H2 _ Hin). clear Hin.
          induction H2; constructor; auto.
        + clear H6 H7. induction H5; auto.
      - eapply EappCase; eauto.
        + clear H2 H3. induction H; eauto.
        + clear H4. induction H0; eauto.
    Qed.

  End wc_exp_ind2.

  Lemma wc_global_NoDup {prefs}:
    forall (g: @global prefs),
      wc_global g ->
      NoDup (map n_name (nodes g)).
  Proof.
    intros * Wc.
    eapply wt_program_NoDup in Wc; eauto.
  Qed.

  Lemma wc_find_node {prefs}:
    forall (G: @global prefs) f n,
      wc_global G ->
      find_node f G = Some n ->
      exists G', wc_node G' n.
  Proof.
    intros G f n' Hwc Hfind.
    apply option_map_inv in Hfind as ((?&?)&(?&?)); subst.
    eapply wt_program_find_unit in Hwc as (?&?); eauto.
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

  Instance wc_exp_Proper {prefs}:
    Proper (@eq (@global prefs) ==> @Permutation.Permutation (ident * clock)
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

  Instance wc_exp_pointwise_Proper {prefs}:
    Proper (@eq (@global prefs) ==> @Permutation.Permutation (ident * clock)
                ==> pointwise_relation _ iff)
           wc_exp.
  Proof.
    intros G G' HG env' env Henv e.
    now rewrite Henv, HG.
  Qed.

  Instance wc_equation_Proper {prefs}:
    Proper (@eq (@global prefs) ==> @Permutation.Permutation (ident * clock)
                ==> @eq equation ==> iff)
           wc_equation.
  Proof with auto.
    intros G1 G2 HG env1 env2 Henv eq1 eq2 Heq; subst.
    destruct eq2 as (xs & es). unfold wc_equation. rewrite Henv.
    split; intros (HA & HB & HC);
      repeat split...
    - setoid_rewrite <- Henv...
    - setoid_rewrite Henv...
  Qed.

  Instance wc_equation_pointwise_Proper {prefs}:
    Proper (@eq (@global prefs) ==> @Permutation.Permutation (ident * clock)
                ==> pointwise_relation _ iff)
           wc_equation.
  Proof.
    intros G1 G2 HG env1 env2 Henv eq; subst. now rewrite Henv.
  Qed.

  Lemma wc_env_Is_free_in_clock_In : forall vars x id ck,
      wc_env vars ->
      In (x, ck) vars ->
      Is_free_in_clock id ck ->
      InMembers id vars.
  Proof.
    intros * Hwenv Hin Hfree.
    unfold wc_env in Hwenv.
    eapply Forall_forall in Hin; eauto; simpl in Hin.
    induction Hfree; inv Hin; eauto using In_InMembers.
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

  (** Adding variables to the environment preserves clocking *)

  Section incl.
    Context {prefs : PS.t}.
    Variable (G : @global prefs).

    Fact wc_clock_incl : forall vars vars' cl,
      incl vars vars' ->
      wc_clock vars cl ->
      wc_clock vars' cl.
    Proof.
      intros vars vars' cl Hincl Hwc.
      induction Hwc; auto.
    Qed.

    Hint Constructors wc_exp.
    Fact wc_exp_incl : forall vars vars' e,
        incl vars vars' ->
        wc_exp G vars e ->
        wc_exp G vars' e .
    Proof with eauto.
      induction e using exp_ind2; intros Hincl Hwc; inv Hwc; eauto;
        econstructor; rewrite Forall_forall in *; eauto.
      1,2:intros ? Hin.
      - specialize (H _ Hin). specialize (H5 _ Hin). rewrite Forall_forall in *; eauto.
      - specialize (H _ Hin); simpl in H. specialize (H8 _ Hin).
        rewrite Forall_forall in *; eauto.
    Qed.

    Fact wc_equation_incl : forall vars vars' eq,
        incl vars vars' ->
        wc_equation G vars eq ->
        wc_equation G vars' eq.
    Proof with eauto.
      intros vars vars' [xs es] Hincl Hwc.
      destruct Hwc as [? [? ?]].
      repeat split...
      - rewrite Forall_forall in *; intros.
        eapply wc_exp_incl...
      - clear H H0.
        eapply Forall2_impl_In; [| eauto].
        intros a b Hin1 Hin2 Hin; simpl in Hin. eapply Hincl...
    Qed.
  End incl.

  (** The global can also be extended ! *)

  Section global_suffix.
    Context {prefs : PS.t}.

    Fact wc_exp_global_suffix : forall (G G': @global prefs) vars e,
      wc_global G ->
      wc_global G' ->
      suffix G G' ->
      wc_exp G vars e ->
      wc_exp G' vars e.
    Proof.
      intros * Hsuffix Hndup1 Hndup2 Wc.
      induction Wc using wc_exp_ind2; econstructor; eauto.
      unfold find_node in *. apply option_map_inv in H3 as ((?&?)&(Hfind&?)); subst.
      erewrite find_unit_suffix_same; eauto. reflexivity.
    Qed.

    Fact wc_equation_global_suffix : forall (G G': @global prefs) vars e,
        wc_global G ->
        wc_global G' ->
        suffix G G' ->
        wc_equation G vars e ->
        wc_equation G' vars e.
    Proof.
      intros G G' vars [xs es] WcG1 WcG2 Hsuff [Hwc1 Hwc2].
      constructor; auto.
      eapply Forall_impl; [|eauto]. intros; eauto using wc_exp_global_suffix.
    Qed.

    Fact wc_node_global_suffix : forall (G G': @global prefs) e,
        wc_global G ->
        wc_global G' ->
        suffix G G' ->
        wc_node G e ->
        wc_node G' e.
    Proof.
      intros * WcG1 WcG2 Hsuff (?&?&?&?).
      repeat constructor; auto.
      eapply Forall_impl; [|eauto]. intros; eauto using wc_equation_global_suffix.
    Qed.

    (** Now that we know this, we can deduce a weaker version of wc_global using Forall: *)
    Lemma wc_global_Forall : forall (G: @global prefs),
        wc_global G ->
        Forall (wc_node G) (nodes G).
    Proof.
      intros G Hwc.
      assert (Hwc':=Hwc).
      assert (exists ns, units G = ns ++ nodes G) as Hsuff by (exists []; reflexivity).
      unfold wc_global, wt_program, units in Hwc; simpl in Hwc.
      induction Hwc; constructor; auto.
      - destruct H as (Wc&Names).
        eapply wc_node_global_suffix in Wc; eauto.
        destruct Hsuff as (?&Hunits).
        apply suffix_intro with (us:=x0++[x]).
        + intros ?; reflexivity.
        + simpl. rewrite <-app_assoc; auto.
      - eapply IHHwc.
        destruct Hsuff as (?&Hunits).
        exists (x0++[x]). rewrite <-app_assoc; auto.
    Qed.
  End global_suffix.

  (** ** Validation *)

  Hint Extern 2 (In _ (idck _)) => apply In_idck_exists.

  Section ValidateExpression.
    Context {prefs : PS.t}.

    Variable G : @global prefs.
    Variable venv : Env.t clock.

    Open Scope option_monad_scope.

    Definition check_var (x : ident) (ck : clock) : bool :=
      match Env.find x venv with
      | None => false
      | Some xc => ck ==b xc
      end.

    Definition check_paired_clocks (nc1 nc2 : nclock) (tc : ann) : bool :=
      match tc with
      | (t, (c, None)) => (fst nc1 ==b c) && (fst nc2 ==b c)
      | _ => false
      end.

    Definition check_merge_clocks {A} (x : ident) (tx : type) (ck : clock) (ncs : list (list nclock)) (n : nat) (tys : list A) : bool :=
      forall2b (fun i ncs => forallb (fun ck' => stripname ck' ==b (Con ck x (tx, i))) ncs
                          && (length ncs ==b length tys)) (seq 0 n) ncs.

    Definition check_case_clocks {A} (ck : clock) (ncs : list (list nclock)) (tys : list A) : bool :=
      forallb (fun ncs => forallb (fun ck' => stripname ck' ==b ck) ncs
                       && (length ncs ==b length tys)) ncs.

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

    Definition check_reset (ckr : list (list nclock)) : bool :=
      forallb (fun cks => match cks with [ck] => true | _ => false end) ckr.

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

      | Eenum _ _ => Some ([(Cbase, None)])

      | Evar x (xt, nc) =>
        match nc with
        | (xc, Some n) => if (check_var x xc) && (x ==b n) then Some [nc] else None
        | (xc, None) => if (check_var x xc) then Some [nc] else None
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

      | Efby e0s es er anns =>
        do nc0s <- oconcat (map check_exp e0s);
        do ncs <- oconcat (map check_exp es);
        do nr <- omap check_exp er;
        if forall3b check_paired_clocks nc0s ncs anns && check_reset nr
        then Some (map snd anns) else None

      | Earrow e0s es er anns =>
        do nc0s <- oconcat (map check_exp e0s);
        do ncs <- oconcat (map check_exp es);
        do nr <- omap check_exp er;
        if forall3b check_paired_clocks nc0s ncs anns && check_reset nr
        then Some (map snd anns) else None

      | Ewhen es x b (tys, nc) =>
        match nc with
        | (Con xc y (_, yb), None) =>
          do nces <- oconcat (map check_exp es);
          if (x ==b y) && (b ==b yb) && (check_var x xc)
             && (forall2b (fun '(c, _) _ => equiv_decb xc c) nces tys)
          then Some (map (fun _ => nc) tys) else None
        | _ => None
        end

      | Emerge (x, tx) es (tys, (ck, None)) =>
        do ncs <- omap (fun es => oconcat (map check_exp es)) es;
        let nc' := (ck, None) in
        if check_var x ck && check_merge_clocks x tx ck ncs (length es) tys
           && (length es <>b 0)
        then Some (map (fun _ => nc') tys) else None

      | Ecase e brs d (tys, (ck, None)) =>
        do nds <- oconcat (map check_exp d);
        do ncs <- omap (or_default_with (Some nds) (fun es => oconcat (map check_exp es))) brs;
        do (ce, _) <- assert_singleton (check_exp e);
        let nc' := (ck, None) in
        if (ce ==b ck) && check_case_clocks ck (nds::ncs) tys
           && (length brs <>b 0)
        then Some (map (fun _ => nc') tys) else None

      | Eapp f es er anns =>
        do n <- find_node f G;
        do nces <- oconcat (map check_exp es);
        do nr <- omap check_exp er;
        do nin0 <- option_map (fun '(_, (_, ck)) => ck) (hd_error n.(n_in));
        do nces0 <- option_map fst (hd_error nces);
        do bck <- find_base_clock nin0 nces0;
        let isub := fold_left2 add_isub n.(n_in) nces (Env.empty ident) in
        let sub := fold_left2 add_osub n.(n_out) anns isub in
        if (forall2b (fun '(_, (_, ck)) '(ck', _) => check_inst bck sub ck ck')
                     n.(n_in) nces)
           && (forall2b (fun '(_, (_, ck)) '(_, (ck', _)) => check_inst bck sub ck ck')
                        n.(n_out) anns)
           && (check_reset nr)
        then Some (map snd anns) else None

      | _ => None end.

    Definition check_nclock (x : ident) (nck : nclock) : bool :=
      let '(ck, nm) := nck in
      check_var x ck && (match nm with
                         | None => true
                         | Some n => n ==b x
                         end).

    Definition check_equation (eq : equation) : bool :=
      let '(xs, es) := eq in
      match oconcat (map check_exp es) with
      | None => false
      | Some ncks => forall2b check_nclock xs ncks
      end.

    Lemma check_var_correct:
      forall x ck,
        check_var x ck = true <-> In (x, ck) (Env.elements venv).
    Proof.
      unfold check_var. split; intros HH.
      - cases_eqn Heq; simpl.
        rewrite equiv_decb_equiv in HH. inv HH.
        take (Env.find _ _ = Some _) and apply Env.elements_correct in it; eauto.
      - apply Env.elements_complete in HH as ->.
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
      forall {A} x tx ck ncs n (tys : list A),
        check_merge_clocks x tx ck ncs n tys = true ->
        Forall2 (fun i => Forall (fun ck' => Con ck x (tx, i) = stripname ck')) (seq 0 n) ncs /\
        Forall (fun ncs => length ncs = length tys) ncs.
    Proof.
      intros * CM; unfold check_merge_clocks in CM.
      rewrite forall2b_Forall2 in CM.
      setoid_rewrite Bool.andb_true_iff in CM.
      setoid_rewrite forallb_Forall in CM.
      split.
      - eapply Forall2_impl_In; [|eauto]. intros ?? _ _ (H&_); simpl in *.
        eapply Forall_impl; [|eauto]. intros (?&?) Heq; simpl in *.
        rewrite equiv_decb_equiv in Heq. inv Heq; auto.
      - eapply Forall2_ignore1 in CM.
        eapply Forall_impl; [|eauto]. intros ? (?&_&_&Hlen).
        rewrite equiv_decb_equiv in Hlen; inv Hlen; auto.
    Qed.

    Lemma check_case_clocks_correct:
      forall {A} ck ncs (tys : list A),
        check_case_clocks ck ncs tys = true ->
        Forall (Forall (fun ck' => ck = stripname ck')) ncs /\
        Forall (fun ncs => length ncs = length tys) ncs.
    Proof.
      intros * CM; unfold check_case_clocks in CM.
      rewrite forallb_Forall in CM.
      setoid_rewrite Bool.andb_true_iff in CM.
      setoid_rewrite forallb_Forall in CM.
      split.
      - eapply Forall_impl; [|eauto]; intros ? (?&_).
        eapply Forall_impl; [|eauto]; intros.
        rewrite equiv_decb_equiv in H0; inv H0; auto.
      - eapply Forall_impl; [|eauto]; intros ? (_&Hlen).
        rewrite equiv_decb_equiv in Hlen; inv Hlen; auto.
    Qed.

    Lemma oconcat_map_check_exp':
      forall {f} es cks,
        (forall e cks,
            In e es ->
            f e = Some cks ->
            wc_exp G (Env.elements venv) e /\ nclockof e = cks) ->
        oconcat (map f es) = Some cks ->
        Forall (wc_exp G (Env.elements venv)) es
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

    Lemma omap_concat_map_check_exp':
      forall {f} ess ncks,
        (forall es e ncks,
            In es ess ->
            In e es ->
            f e = Some ncks ->
            wc_exp G (Env.elements venv) e /\ nclockof e = ncks) ->
        omap (fun es => oconcat (map f es)) ess = Some ncks ->
        Forall (Forall (wc_exp G (Env.elements venv))) ess
        /\ Forall2 (fun es ncks => nclocksof es = ncks) ess ncks.
    Proof.
      induction ess as [|es ess IH]; intros ncks WTf CE. now inv CE; auto.
      simpl in CE. destruct (oconcat (map f es)) eqn:Ce; [|now omonadInv CE].
      eapply oconcat_map_check_exp' in Ce as (?&?); eauto with datatypes.
      destruct (omap _ _) as [tes|]; [|now omonadInv CE].
      omonadInv CE. simpl.
      specialize (IH tes) as (? & ?); eauto using in_cons.
    Qed.

    Lemma omap_concat_map_check_exp'':
      forall {f} nds ess ncks,
        (forall es e ncks,
            In (Some es) ess ->
            In e es ->
            f e = Some ncks ->
            wc_exp G (Env.elements venv) e /\ nclockof e = ncks) ->
        omap (or_default_with (Some nds) (fun es => oconcat (map f es))) ess = Some ncks ->
        Forall (LiftO True (Forall (wc_exp G (Env.elements venv)))) ess
        /\ Forall2 (fun es ncks => LiftO True (fun es => nclocksof es = ncks) es) ess ncks.
    Proof.
      induction ess as [|es ess IH]; intros ncks WTf CE. now inv CE; auto.
      destruct es; simpl in *.
      - destruct (oconcat (map _ l)) eqn:Ce; [|now omonadInv CE].
        destruct (omap _ _) as [tes|] eqn:CE''; [|now omonadInv CE].
        omonadInv CE. simpl.
        eapply oconcat_map_check_exp' in Ce as (?&?); eauto with datatypes.
        specialize (IH tes) as (? & ?); eauto using in_cons.
      - destruct (omap _ _) as [tes|] eqn:CE'; [|now omonadInv CE].
        omonadInv CE. simpl.
        specialize (IH tes) as (? & ?); eauto using in_cons.
        split; constructor; simpl; auto.
    Qed.

    Lemma omap_check_exp':
      forall {f} es cks,
        (forall e cks,
            In e es ->
            f e = Some cks ->
            wc_exp G (Env.elements venv) e /\ nclockof e = cks) ->
        omap f es = Some cks ->
        Forall (wc_exp G (Env.elements venv)) es
        /\ Forall2 (fun e ck => nclockof e = ck) es cks.
    Proof.
      induction es as [|e es IH]; intros cks WTf CE. now inv CE; auto.
      simpl in CE. destruct (f e) eqn:Ce; [|now omonadInv CE].
      destruct (omap f es) as [ces|]; [|now omonadInv CE].
      omonadInv CE. simpl.
      apply WTf in Ce as (Ce1 & Ce2); auto with datatypes.
      destruct (IH ces) as (? & ?); auto.
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
      induction xs as [|(y, (yt, yc)) xs IH]; simpl; auto.
      - destruct anns; auto.
      - simpl; intros anns sub NIx.
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
      induction xs as [|(y, (yt, yc)) xs IH]; simpl; auto.
      - destruct ncs; auto.
      - simpl; intros ncs sub NIx.
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
      intros sub Fx. cases_eqn Heq.
      1,2:repeat take (_ && _ = true) and apply andb_prop in it as (? & ?).
      1,2:repeat take ((_ ==b _) = true) and rewrite equiv_decb_equiv in it; inv it.
      1,2:erewrite IHxc in Heq0; [|eauto]; inv Heq0; auto.
    Qed.

    Lemma check_reset_correct: forall cks,
        check_reset cks = true ->
        Forall (fun cks => exists ck, cks = [ck]) cks.
    Proof.
      intros * Che.
      eapply forallb_Forall in Che.
      eapply Forall_impl; [|eauto]. intros ? Eq.
      destruct a as [|? [|? ?]]; try congruence; eauto.
    Qed.

    Local Hint Constructors wc_exp.
    Lemma check_exp_correct:
      forall e ncks,
        check_exp e = Some ncks ->
        wc_exp G (Env.elements venv) e
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
               | p:(_ * _) |- _ => destruct p
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
               | H:(match ?o with Some _ => if _ then _ else _ | None => _ end) = Some _ |- _ =>
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
      - (* Econst *) eauto.
      - (* Eenum *) eauto.
      - (* Evar *) eauto.
      - (* Evar *) eauto.
      - (* Eunop *)
        apply IHe in OE0 as (? & ?).
        eauto using nclockof_clockof.
      - (* Ebinop *)
        apply IHe1 in OE0 as (? & ?); apply IHe2 in OE1 as (? & ?).
        eauto using nclockof_clockof.
      - (* Efby *)
        repeat take (Forall (fun e :exp => _) _) and rewrite Forall_forall in it.
        apply oconcat_map_check_exp' in OE0 as (? & ?); auto.
        apply oconcat_map_check_exp' in OE1 as (? & ?); auto. subst.
        apply omap_check_exp' in OE2 as (? & ?); auto. subst.
        repeat take (map stripname _ = map clock_of_nclock _)
               and rewrite <-clocksof_nclocksof in it.
        split; eauto. econstructor; eauto.
        eapply check_reset_correct in H3.
        eapply Forall2_ignore1' in H3. 2:symmetry; eapply Forall2_length; eauto.
        eapply Forall2_Forall2, Forall2_ignore2 in H6; eauto.
        eapply Forall_impl; [|eauto]. intros ? (?&?&(?&?)&?); subst.
        rewrite clockof_nclockof, H7; simpl; eauto.
      - (* Earrow *)
        repeat take (Forall (fun e :exp => _) _) and rewrite Forall_forall in it.
        apply oconcat_map_check_exp' in OE0 as (? & ?); auto.
        apply oconcat_map_check_exp' in OE1 as (? & ?); auto. subst.
        apply omap_check_exp' in OE2 as (? & ?); auto. subst.
        repeat take (map stripname _ = map clock_of_nclock _)
               and rewrite <-clocksof_nclocksof in it.
        split; eauto. econstructor; eauto.
        eapply check_reset_correct in H3.
        eapply Forall2_ignore1' in H3. 2:symmetry; eapply Forall2_length; eauto.
        eapply Forall2_Forall2, Forall2_ignore2 in H6; eauto.
        eapply Forall_impl; [|eauto]. intros ? (?&?&(?&?)&?); subst.
        rewrite clockof_nclockof, H7; simpl; eauto.
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
        take (Forall _ es) and (repeat setoid_rewrite Forall_forall in it).
        take (omap _ _ = Some _) and
             apply omap_concat_map_check_exp' in it as (? & ?); eauto.
        take (check_merge_clocks _ _ _ _ _ _ = true) and
             apply check_merge_clocks_correct in it as (? & ?).
        split; eauto. econstructor; eauto.
        + contradict H1; subst; simpl. apply Bool.not_true_iff_false.
          apply nequiv_decb_false, equiv_decb_equiv. constructor.
        + eapply Forall2_swap_args, Forall2_trans_ex in H3; eauto.
          eapply Forall2_impl_In; [|eauto]. intros ?? _ _ (?&_&Hf&?); subst.
          rewrite clocksof_nclocksof, Forall_map.
          assumption.
        + clear - H3 H4.
          induction H3; inv H4; constructor; auto.
          rewrite clocksof_nclocksof, map_length; auto.
      - (* Ecase *)
        take (Forall _ _) and (repeat setoid_rewrite Forall_forall in it).
        take (oconcat (map check_exp _) = Some _) and
             apply oconcat_map_check_exp' in it as (? & ?); eauto.
        take (omap _ _ = Some _) and
             apply omap_concat_map_check_exp'' in it as (? & ?); eauto.
        take (check_case_clocks _ _ _ = true) and
             apply check_case_clocks_correct in it as (? & ?).
        eapply forallb_Forall in H3.
        eapply IHe in AS as (? & ?); auto.
        split; eauto. econstructor; eauto.
        + now rewrite clockof_nclockof, H10.
        + contradict H2; subst; simpl. apply Bool.not_true_iff_false.
          apply nequiv_decb_false, equiv_decb_equiv. constructor.
        + intros. eapply Forall_forall in H5; eauto. simpl in H5; auto.
        + intros. clear - H4 H6 H11.
          eapply Forall2_ignore2 in H6.
          eapply Forall_forall in H6 as (?&?&?); eauto; simpl in *.
          eapply Forall_forall in H4; eauto.
          rewrite clocksof_nclocksof, Forall_map.
          congruence.
        + intros. clear - H8 H6 H11.
          eapply Forall2_ignore2 in H6.
          eapply Forall_forall in H6 as (?&?&?); eauto; simpl in *.
          eapply Forall_forall in H8; eauto.
          rewrite clocksof_nclocksof, map_length.
          congruence.
        + rewrite clocksof_nclocksof, H1.
          rewrite Forall_map. eapply Forall_impl; [|eauto].
          intros ? Heq; simpl in *.
          rewrite equiv_decb_equiv in Heq; inv Heq; auto.
        + rewrite clocksof_nclocksof, map_length. congruence.
        + intros ??? Hin1 Hin2 Hce.
          eapply Forall_forall in H; eauto; simpl in H.
          eapply Forall_forall in H; eauto.
      - (* Eapp *)
        repeat take (Forall _ _) and rewrite Forall_forall in it.
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
          rewrite Permutation_swap in ND. apply NoDupMembers_app_r in ND.
          rewrite app_assoc in ND. apply NoDupMembers_app_l in ND. auto. }

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
          pose proof (NoDupMembers_app_l _ _ (NoDupMembers_app_r _ _ (NoDupMembers_app_r _ _ n.(n_nodup)))).
          rewrite fold_left2_add_osub with (1:=Ix); auto.
          setoid_rewrite Env.Props.P.F.not_find_in_iff.
          rewrite fold_left2_add_isub_skip; auto using Env.gempty.
          rewrite <-fst_InMembers.
          apply in_combine_l, In_InMembers in Ix.
          apply NoDupMembers_app_InMembers with (2:=Ix).
          rewrite Permutation_app_comm.
          pose proof n.(n_nodup) as ND.
          rewrite Permutation_swap in ND. apply NoDupMembers_app_r in ND.
          rewrite app_assoc in ND. apply NoDupMembers_app_l in ND. auto. }

        eapply omap_check_exp' in OE2 as (? & ?); eauto.
        econstructor; eauto.
        eapply check_reset_correct in H2.
        eapply Forall2_ignore1' in H2. 2:symmetry; eapply Forall2_length; eauto.
        eapply Forall2_Forall2, Forall2_ignore2 in H4; eauto.
        eapply Forall_impl; [|eauto]. intros ? (?&?&(?&?)&?); subst.
        rewrite clockof_nclockof, H7; simpl; eauto.
    Qed.

    Lemma oconcat_map_check_exp:
      forall es ncks,
        oconcat (map check_exp es) = Some ncks ->
        Forall (wc_exp G (Env.elements venv)) es
        /\ nclocksof es = ncks.
    Proof.
      induction es as [|e es IH]; intros ncks CE. now inv CE; eauto.
      simpl in CE. cases_eqn Heq.
      take (check_exp _ = Some _) and rename it into CWF.
      apply check_exp_correct in CWF as (WCe & NCe).
      destruct (oconcat (map check_exp es)) eqn:CWF; inv CE.
      specialize (IH _ eq_refl) as (? & ?).
      split; auto.
      simpl. take (nclocksof _ = _) and rewrite it. eauto.
    Qed.

    Lemma check_equation_correct:
      forall eq,
        check_equation eq = true ->
        wc_equation G (Env.elements venv) eq.
    Proof.
      intros eq CE. destruct eq as (xs, es); simpl in CE.
      cases_eqn Heq.
      take (oconcat (map _ _) = Some _)
      and apply oconcat_map_check_exp in it as (WC & NC).
      subst. apply forall2b_Forall2 in CE.
      constructor; auto.
      rewrite clocksof_nclocksof, Forall2_map_2.
      split; apply Forall2_impl_In with (2:=CE); intros x (ck, nm) Ix Inc CNC;
        simpl in *; cases_eqn Heq;
        apply Bool.andb_true_iff in CNC as (CNC1 & CNC2);
        take (check_var _ _ = true) and apply check_var_correct in it;
        simpl; auto.
      now rewrite equiv_decb_equiv in CNC2.
    Qed.

  End ValidateExpression.

  Section ValidateGlobal.

    Fixpoint check_clock xenv (ck : clock) : bool :=
      match ck with
      | Cbase => true
      | Con ck' x b =>
        check_var xenv x ck' && check_clock xenv ck'
      end.

    Definition check_env (env : list (ident * clock)) : bool :=
      forallb (check_clock (Env.from_list env)) (List.map snd env).

    Definition check_node {prefs} (G : @global prefs) (n : @node prefs) :=
      check_env (idck (n_in n)) &&
      check_env (idck (n_in n ++ n_out n)) &&
      check_env (idck (n_in n ++ n_out n ++ n_vars n)) &&
      forallb (check_equation G (Env.from_list (idck (n_in n ++ n_vars n ++ n_out n)))) (n_eqs n).

    Definition check_global {prefs} (G : @global prefs) :=
      check_nodup (List.map n_name G.(nodes)) &&
      (fix aux nds := match nds  with
                      | [] => true
                      | hd::tl => check_node (update G tl) hd && aux tl
                      end) G.(nodes).

    Lemma check_clock_correct : forall xenv ck,
        check_clock xenv ck = true ->
        wc_clock (Env.elements xenv) ck.
    Proof.
      induction ck; intros Hcheck; simpl; auto.
      apply Bool.andb_true_iff in Hcheck as [Hc1 Hc2].
      constructor; auto.
      rewrite check_var_correct in Hc1; auto.
    Qed.

    Lemma check_env_correct : forall env,
        check_env env = true ->
        wc_env env.
    Proof.
      intros env Hcheck.
      unfold wc_env, check_env in *.
      apply forallb_Forall, Forall_map in Hcheck.
      eapply Forall_impl; eauto; intros ? Hc; simpl in Hc.
      apply check_clock_correct in Hc.
      eapply wc_clock_incl; eauto.
      apply Env.elements_from_list_incl.
    Qed.

    Lemma check_node_correct {prefs} : forall (G : @global prefs) n,
        check_node G n = true ->
        wc_node G n.
    Proof.
      intros * Hcheck.
      unfold check_node in Hcheck.
      repeat rewrite Bool.andb_true_iff in Hcheck. destruct Hcheck as [[[Hc1 Hc2] Hc3] Hc4].
      repeat constructor.
      1-3:apply check_env_correct; auto.
      apply forallb_Forall in Hc4.
      eapply Forall_impl; [|eauto]. intros ? Hcheck; simpl in Hcheck.
      apply check_equation_correct in Hcheck.
      eapply wc_equation_incl; eauto.
      apply Env.elements_from_list_incl.
    Qed.

    Lemma check_global_correct {prefs} : forall (G : @global prefs),
        check_global G = true ->
        wc_global G.
    Proof.
      intros G Hcheck.
      apply Bool.andb_true_iff in Hcheck; destruct Hcheck as [Hndup Hcheck].
      apply check_nodup_correct in Hndup.
      unfold wc_global, wt_program, units; simpl.
      induction (nodes G); constructor; inv Hndup.
      1-3:simpl in Hcheck; apply Bool.andb_true_iff in Hcheck as [Hc1 Hc2]; auto.
      split.
      - apply check_node_correct in Hc1; auto using Env.elements_from_list_incl.
      - apply Forall_forall. intros ? Hin contra.
        apply H1. rewrite in_map_iff. exists x; split; auto.
    Qed.

  End ValidateGlobal.

  (** *** Some additional properties related to remove_member *)

  Definition remove_member {B} := @remove_member _ B Common.EqDec_instance_0.

  (* Its possible to remove ids not present in a clock from the typing environment *)
  Lemma wc_clock_nfreein_remove : forall vars id ck,
      ~Is_free_in_clock id ck ->
      wc_clock vars ck ->
      wc_clock (remove_member id vars) ck.
  Proof.
    intros vars id ck Hnfree Hwc.
    induction Hwc; constructor.
    - apply IHHwc.
      intro Hfree'. apply Hnfree; constructor; auto.
    - clear IHHwc Hwc.
      eapply remove_member_neq_In; eauto.
      intro contra; subst. apply Hnfree. constructor.
  Qed.

  Lemma wc_env_nfreein_remove : forall id vars,
      NoDupMembers vars ->
      wc_env vars ->
      Forall (fun '(_, ck) => ~Is_free_in_clock id ck) vars ->
      wc_env (remove_member id vars).
  Proof.
    intros id vars Hndup Hwc Hfree.
    unfold wc_env in Hwc.
    eapply Forall_Forall in Hwc; eauto.
    eapply Forall_incl. 2:eapply remove_member_incl.
    eapply Forall_impl; eauto.
    intros [id' ck'] H; simpl in H; destruct H as [H1 H2].
    eapply wc_clock_nfreein_remove in H1; simpl; eauto.
  Qed.

  Lemma wc_clock_nfreein_remove' : forall vars id ck ck',
      ~Is_free_in_clock id ck' ->
      wc_clock ((id, ck)::vars) ck' ->
      wc_clock vars ck'.
  Proof.
    intros vars id ck ck' Hnfree Hwc.
    induction Hwc; constructor.
    - apply IHHwc.
      intro Hfree'. apply Hnfree; constructor; auto.
    - clear IHHwc Hwc.
      inv H; auto.
      exfalso. inv H0.
      apply Hnfree. constructor.
  Qed.

  Fact clock_parent_In : forall vars ck ck' id b,
      wc_clock vars ck ->
      clock_parent (Con ck' id b) ck ->
      In (id, ck') vars.
  Proof.
    induction ck; intros * Hwc Hparent; inv Hwc; inv Hparent; eauto.
    inv H1; eauto.
  Qed.

  (** The clock of a var cant depend on its var *)
  Lemma wc_nfree_in_clock : forall vars ck id,
      NoDupMembers vars ->
      In (id, ck) vars ->
      wc_clock vars ck ->
      ~Is_free_in_clock id ck.
  Proof.
    intros vars ck id Hndup Hin Hwc contra.
    apply Is_free_in_clock_self_or_parent in contra as [ck' [b [H|H]]]; subst.
    - inv Hwc.
      eapply NoDupMembers_det in Hndup. 2:eapply H3. 2:eapply Hin.
      apply clock_not_in_clock in Hndup; auto.
    - assert (In (id, ck') vars) as Hin' by (eapply clock_parent_In; eauto).
      apply clock_parent_parent' in H.
      apply clock_parent_no_loops in H.
      eapply NoDupMembers_det in Hndup. 2:eapply Hin. 2:eapply Hin'. congruence.
  Qed.

  (** *** A clock dependency order *)

  Inductive dep_ordered_clocks : list (ident * clock) -> Prop :=
  | dep_ord_clock_nil : dep_ordered_clocks nil
  | dep_ord_clock_cons : forall ck id ncks,
      dep_ordered_clocks ncks ->
      ~Exists (Is_free_in_clock id) (map snd ncks) ->
      dep_ordered_clocks ((id, ck)::ncks).

  Program Fixpoint wc_env_dep_ordered (vars : list (ident * clock)) {measure (length vars)} :
      NoDupMembers vars ->
      wc_env vars ->
      exists vars', Permutation vars vars' /\ dep_ordered_clocks vars' := _.
  Next Obligation.
    rename H into Hndup. rename H0 into Hwc.
    specialize (exists_child_clock' vars Hndup Hwc) as [?|[id [ck [Hin Hfree]]]]; subst; simpl.
    - exists []. split; auto. constructor.
    - remember (remove_member id vars) as vars'.
      assert (NoDupMembers vars') as Hndup'.
      { subst. apply remove_member_NoDupMembers; eauto. }
      assert (wc_env vars') as Hwc'.
      { subst. eapply wc_env_nfreein_remove; eauto. }
      assert (length vars' < length vars) as Hlen.
      { rewrite Heqvars'.
        specialize (remove_member_Perm Common.EqDec_instance_0 _ _ _ Hndup Hin) as Hperm. symmetry in Hperm.
        apply Permutation_length in Hperm. rewrite Hperm; simpl. apply PeanoNat.Nat.lt_succ_diag_r. }
      specialize (wc_env_dep_ordered _ Hlen Hndup' Hwc') as [vars'' [Hperm Hdep]].
      exists ((id, ck)::vars''). split; auto.
      + rewrite <- Hperm, Heqvars'.
        setoid_rewrite remove_member_Perm; eauto.
      + simpl. constructor; simpl; eauto.
        rewrite <- Forall_Exists_neg, Forall_map, <- Hperm, Heqvars'.
        eapply Forall_incl. 2:eapply remove_member_incl.
        eapply Forall_impl; eauto.
        intros [id' ck'] H; auto.
  Qed.

  Fact wc_clock_dep_ordered_remove : forall id ck x xs,
      NoDupMembers (x::xs) ->
      In (id, ck) xs ->
      dep_ordered_clocks (x::xs) ->
      wc_clock (x::xs) ck ->
      wc_clock xs ck.
  Proof.
    intros id ck [id' ck'] xs Hndup Hin Hdep Hwc.
    eapply wc_clock_nfreein_remove with (id:=id') in Hwc.
    - simpl in Hwc.
      destruct Common.EqDec_instance_0 in Hwc; try congruence.
      inv Hndup.
      unfold remove_member in Hwc. rewrite remove_member_nIn_idem in Hwc; auto.
    - inv Hdep. rewrite <- Forall_Exists_neg, Forall_forall in H3.
      eapply H3. rewrite in_map_iff. exists (id, ck); auto.
  Qed.

  Corollary wc_env_dep_ordered_remove : forall x xs,
      NoDupMembers (x::xs) ->
      dep_ordered_clocks (x::xs) ->
      wc_env (x::xs) ->
      wc_env xs.
  Proof with eauto.
    intros [id' ck'] xs Hndup Hdep Hwc.
    unfold wc_env in *. inv Hwc.
    eapply Forall_impl_In; [| eauto]. intros [id ck] Hin Hwc.
    eapply wc_clock_dep_ordered_remove in Hwc...
  Qed.

  (** *** Another equivalent clock dependency order *)

  Definition only_depends_on (vars : list ident) (ck : clock) :=
    forall id, Is_free_in_clock id ck -> In id vars.

  Lemma only_depends_on_Con : forall vars ck id b,
      only_depends_on vars (Con ck id b) ->
      only_depends_on vars ck.
  Proof.
    intros vars ck id b Hon id' Hisfree.
    apply Hon. constructor; auto.
  Qed.

  Lemma only_depends_on_incl : forall vars vars' ck,
      incl vars vars' ->
      only_depends_on vars ck ->
      only_depends_on vars' ck.
  Proof.
    intros vars vars' ck Hincl Honly id Hfree. eauto.
  Qed.

  Lemma wc_clock_only_depends_on : forall vars ck,
      wc_clock vars ck ->
      only_depends_on (map fst vars) ck.
  Proof.
    intros vars ck Hwc id Hisfree; induction Hwc; inv Hisfree; eauto.
    rewrite in_map_iff. exists (x, ck); auto.
  Qed.

  Inductive dep_ordered_on : list (ident * clock) -> Prop :=
  | dep_ordered_nil : dep_ordered_on []
  | dep_ordered_cons : forall nck ncks,
      dep_ordered_on ncks ->
      only_depends_on (map fst ncks) (snd nck) ->
      dep_ordered_on (nck::ncks).

  Lemma dep_ordered_on_InMembers : forall ncks,
      dep_ordered_on ncks ->
      Forall (fun ck => forall id, Is_free_in_clock id ck -> InMembers id ncks) (map snd ncks).
  Proof.
    intros ncks Hdep. induction Hdep; simpl; constructor.
    - intros id Hfree.
      destruct nck as [id' ck']; simpl in *.
      apply H in Hfree.
      right. rewrite fst_InMembers; auto.
    - rewrite Forall_map in *.
      eapply Forall_impl; eauto.
      intros [id ck] Hin id' Hisfree; simpl in *.
      destruct nck as [id'' ck''].
      apply Hin in Hisfree; auto.
  Qed.

  Lemma dep_ordered_dep_ordered_on : forall ncks,
      NoDupMembers ncks ->
      wc_env ncks ->
      dep_ordered_clocks ncks ->
      dep_ordered_on ncks.
  Proof with eauto.
    induction ncks; intros Hndup Hwc Hdep; [constructor|].
    inv Hndup. inv Hdep. constructor; simpl.
    - eapply IHncks...
      eapply wc_env_dep_ordered_remove with (x:=(a0, b)) in Hwc...
      1,2:constructor...
    - inv Hwc; simpl in *.
      eapply wc_clock_only_depends_on, wc_clock_no_loops_remove...
  Qed.

  Lemma dep_ordered_on_dep_ordered : forall ncks,
      NoDupMembers ncks ->
      wc_env ncks ->
      dep_ordered_on ncks ->
      dep_ordered_clocks ncks.
  Proof with eauto.
    induction ncks as [|[id ck]]; intros Hndup Hwc Hdep; [constructor|].
    assert (Hndup':=Hndup). inv Hndup'; inv Hdep. simpl in *; constructor.
    - apply IHncks...
      eapply wc_env_nfreein_remove with (id:=id) in Hwc.
      + simpl in *. destruct Common.EqDec_instance_0 in Hwc; try congruence.
        unfold remove_member in Hwc. rewrite remove_member_nIn_idem in Hwc...
      + constructor...
      + constructor.
        * eapply wc_nfree_in_clock in Hndup... 1:constructor...
           inv Hwc...
        * apply dep_ordered_on_InMembers in H2.
          rewrite Forall_map in H2.
          eapply Forall_impl; eauto. intros [? ?] ? contra.
          apply H in contra. congruence.
    - apply dep_ordered_on_InMembers in H2.
      rewrite <- Forall_Exists_neg.
      eapply Forall_impl; eauto.
      intros a H; simpl in H.
      intro contra. apply H in contra. congruence.
  Qed.

  Corollary dep_ordered_iff : forall vars,
      NoDupMembers vars ->
      wc_env vars ->
      (dep_ordered_clocks vars <-> dep_ordered_on vars).
  Proof with eauto.
    intros. split.
    - eapply dep_ordered_dep_ordered_on...
    - eapply dep_ordered_on_dep_ordered...
  Qed.

  Corollary wc_env_dep_ordered_on_remove : forall x xs,
      NoDupMembers (x::xs) ->
      dep_ordered_on (x::xs) ->
      wc_env (x::xs) ->
      wc_env xs.
  Proof with eauto.
    intros x xs Hndup Hdep Hwenv.
    apply dep_ordered_on_dep_ordered in Hdep...
    eapply wc_env_dep_ordered_remove...
  Qed.

  Corollary wc_env_dep_ordered_on : forall vars,
      NoDupMembers vars ->
      wc_env vars ->
      exists vars', Permutation vars vars' /\ dep_ordered_on vars'.
  Proof.
    intros vars Hndup Hwenv.
    specialize (wc_env_dep_ordered vars Hndup Hwenv) as [vars' [Hperm Hdep]].
    exists vars'. split; auto.
    eapply dep_ordered_dep_ordered_on in Hdep; eauto.
    - rewrite <- Hperm; auto.
    - rewrite <- Hperm; auto.
  Qed.

  Instance only_depends_on_Proper:
    Proper (@Permutation.Permutation ident ==> @eq clock ==> iff)
           only_depends_on.
  Proof.
    intros vars vars' Hperm ck ck' ?; subst.
    unfold only_depends_on.
    split; intros; [rewrite <- Hperm|rewrite Hperm]; eauto.
  Qed.

  (** *** Additional properties about WellInstantiated *)

  Definition anon_streams (l : list nclock) : list (ident * clock) :=
    map_filter (fun '(ck, id) => match id with
                              | None => None
                              | Some id => Some (id, ck)
                              end) l.

  Lemma anon_streams_anon_streams : forall (anns : list ann),
      anon_streams (map snd anns) = idck (Syn.anon_streams anns).
  Proof.
    induction anns; simpl; auto.
    destruct a as [ty [ck [id|]]]; simpl; congruence.
  Qed.

  Fact WellInstantiated_sub_fsts : forall bck sub ins outs,
      Forall2 (WellInstantiated bck sub) ins outs ->
      map_filter sub (map fst ins) = (map fst (anon_streams outs)).
  Proof.
    intros bck sub ins outs Hinst.
    induction Hinst; simpl; auto.
    destruct H as [Hsub _]; destruct y as [ck id]; simpl in *; subst.
    destruct sub; simpl; [f_equal|]; auto.
  Qed.

  Lemma instck_only_depends_on : forall vars bck bckvars sub ck ck',
      only_depends_on bckvars bck ->
      only_depends_on vars ck ->
      instck bck sub ck = Some ck' ->
      only_depends_on (bckvars++map_filter sub vars) ck'.
  Proof with eauto.
    induction ck; intros ck' Hbck Hdep Hinst; simpl in *.
    - inv Hinst...
      eapply only_depends_on_incl; eauto. apply incl_appl, incl_refl.
    - destruct instck eqn:Hinst'; try congruence.
      destruct sub eqn:Hsub; try congruence.
      inv Hinst.
      specialize (only_depends_on_Con _ _ _ _ Hdep) as Hdep'.
      specialize (IHck _ Hbck Hdep' eq_refl).
      intros id Hfree. inv Hfree.
      + specialize (Hdep i (FreeCon1 _ _ _)).
        apply in_or_app; right.
        eapply map_filter_In; eauto.
      + apply IHck...
  Qed.

  (** *** Relation between nclocksof and fresh_ins *)

  Lemma anon_streams_nclockof_fresh_in {prefs} : forall (G: @global prefs) vars e,
      wc_exp G vars e ->
      incl (anon_streams (nclockof e)) (vars++idck (fresh_in e)).
  Proof with eauto.
    induction e using exp_ind2; intros Hwc;
      inv Hwc; simpl; try apply incl_nil'.
    - (* var *)
      rewrite app_nil_r.
      intros id Hin; inv Hin... inv H.
    - (* fby *)
      replace (anon_streams _) with (@nil (ident * clock)).
      2: { clear - H12.
           induction a; simpl; auto. inv H12.
           rewrite <- IHa... unfold unnamed_stream in H1.
           destruct a as [ty [ck id]]; simpl in *; subst. reflexivity. }
      apply incl_nil'.
    - (* arrow *)
      replace (anon_streams _) with (@nil (ident * clock)).
      2: { clear - H12.
           induction a; simpl; auto. inv H12.
           rewrite <- IHa... unfold unnamed_stream in H1.
           destruct a as [ty [ck id]]; simpl in *; subst. reflexivity. }
      apply incl_nil'.
     - (* when *)
      replace (anon_streams _) with (@nil (ident * clock)).
      2: { clear - tys. induction tys; simpl; auto. }
      apply incl_nil'.
    - (* merge *)
      replace (anon_streams _) with (@nil (ident * clock)).
      2: { clear - tys. induction tys; simpl; auto. }
      apply incl_nil'.
    - (* case *)
      replace (anon_streams _) with (@nil (ident * clock)).
      2: { clear - tys. induction tys; simpl; auto. }
      apply incl_nil'.
    - (* app *)
      unfold idck. repeat rewrite map_app.
      apply incl_appr, incl_appr, incl_appr.
      rewrite anon_streams_anon_streams. reflexivity.
  Qed.

  Corollary anon_streams_nclocksof_fresh_ins prefs : forall (G: @global prefs) vars es,
      Forall (wc_exp G vars) es ->
      incl (anon_streams (nclocksof es)) (vars++idck (fresh_ins es)).
  Proof with eauto.
    induction es; intros Hf; inv Hf; simpl.
    - eapply incl_nil'.
    - unfold anon_streams. rewrite map_filter_app.
      apply incl_app.
      + etransitivity. eapply anon_streams_nclockof_fresh_in in H1...
        unfold fresh_ins, idck; simpl.
        apply incl_appr', incl_map, incl_appl, incl_refl.
      + etransitivity...
        unfold fresh_ins, idck; simpl.
        apply incl_appr', incl_map, incl_appr, incl_refl.
  Qed.

  (** *** wc_exp implies wc_clock *)

  Definition preserving_sub bck (sub : ident -> option ident) (vars vars' : list (ident * clock)) dom :=
    Forall (fun i => forall i' ck ck',
                sub i = Some i' ->
                instck bck sub ck = Some ck' ->
                In (i, ck) vars ->
                In (i', ck') vars'
           ) dom.

  Fact preserving_sub_incl1 : forall bck sub vars1 vars1' vars2 dom,
      incl vars1' vars1 ->
      preserving_sub bck sub vars1 vars2 dom ->
      preserving_sub bck sub vars1' vars2 dom.
  Proof.
    intros bck sub vars1 vars1' vars2 dom Hincl Hpre.
    unfold preserving_sub in *.
    eapply Forall_impl; eauto.
    intros; eauto.
  Qed.

  Fact preserving_sub_incl2 : forall bck sub vars1 vars2 vars2' dom,
      incl vars2 vars2' ->
      preserving_sub bck sub vars1 vars2 dom ->
      preserving_sub bck sub vars1 vars2' dom.
  Proof.
    intros bck sub vars1 vars2 vars2' dom Hincl Hpre.
    unfold preserving_sub in *.
    eapply Forall_impl; eauto.
    intros; eauto.
  Qed.

  Fact preserving_sub_incl3 : forall bck sub vars vars' dom dom',
      incl dom dom' ->
      preserving_sub bck sub vars vars' dom' ->
      preserving_sub bck sub vars vars' dom.
  Proof.
    intros bck sub vars vars' dom dom' Hincl Hpre.
    unfold preserving_sub in *.
    eapply Forall_incl; eauto.
  Qed.

  Instance preserving_sub_Proper:
    Proper (@eq clock ==> @eq (ident -> option ident)
                ==> @Permutation (ident * clock) ==> @Permutation (ident * clock) ==> @Permutation ident
                ==> iff)
           preserving_sub.
  Proof.
    intros bck bck' ? sub sub' ?; subst.
    intros vars1 vars1' Hperm1 vars2 vars2' Hperm2 dom dom' Hperm3.
    split; intro H.
    1,2:eapply preserving_sub_incl1 in H. 2:rewrite Hperm1. 4:rewrite <- Hperm1. 2,4:reflexivity.
    1,2:eapply preserving_sub_incl2 in H. 2:rewrite Hperm2. 4:rewrite <- Hperm2. 2,4:reflexivity.
    1,2:eapply preserving_sub_incl3 in H. 2:rewrite Hperm3. 4:rewrite <- Hperm3. 2,4:reflexivity.
    1,2:assumption.
  Qed.

  Fixpoint frees_in_clock (ck : clock) :=
    match ck with
    | Cbase => []
    | Con ck' id _ => id::(frees_in_clock ck')
    end.

  Lemma Is_free_in_frees_in_clock : forall ck,
      Forall (fun id => Is_free_in_clock id ck) (frees_in_clock ck).
  Proof with eauto.
    induction ck; simpl; constructor.
    - constructor.
    - eapply Forall_impl...
      intros a H; simpl in H. constructor...
  Qed.

  Lemma only_depends_on_frees_in_clock : forall vars ck,
      only_depends_on vars ck ->
      incl (frees_in_clock ck) vars.
  Proof.
    induction ck; intros Hdep; simpl.
    - apply incl_nil'.
    - apply incl_cons.
      + apply Hdep, FreeCon1.
      + eapply IHck, only_depends_on_Con, Hdep.
  Qed.

  Fact instck_wc_clock : forall vars vars' bck sub ck ck',
      wc_clock vars ck ->
      wc_clock vars' bck ->
      preserving_sub bck sub vars vars' (frees_in_clock ck) ->
      instck bck sub ck = Some ck' ->
      wc_clock vars' ck'.
  Proof with eauto.
    intros vars vars' bck sub.
    induction ck; intros ck' Hwc Hwcb Hpre Hinst; simpl in *.
    - inv Hinst...
    - inv Hwc.
      destruct (instck bck sub ck) eqn:Hinst'; try congruence.
      assert (preserving_sub bck sub vars vars' (frees_in_clock ck)) as Hpre'.
      { eapply preserving_sub_incl3; eauto. apply incl_tl, incl_refl. }
      specialize (IHck _ H1 Hwcb Hpre' eq_refl).
      unfold preserving_sub in Hpre; rewrite Forall_forall in Hpre.
      destruct (sub i) eqn:Hsub; try congruence.
      inv Hinst. constructor...
      eapply Hpre... left...
  Qed.

  Fact WellInstantiated_wc_clock : forall vars vars' sub bck id ck ck' name,
      wc_clock vars ck ->
      wc_clock vars' bck ->
      preserving_sub bck sub vars vars' (frees_in_clock ck) ->
      WellInstantiated bck sub (id, ck) (ck', name) ->
      wc_clock vars' ck'.
  Proof.
    intros vars vars' sub bck id ck ck' name Hwc Hwcb Hpre Hinst.
    destruct Hinst as [Hsub Hinst]; simpl in *.
    eapply instck_wc_clock in Hinst; eauto.
  Qed.

  Lemma WellInstantiated_wc_clocks' : forall vars' bck sub xs ys,
      NoDupMembers xs ->
      dep_ordered_on xs ->
      wc_clock vars' bck ->
      wc_env xs ->
      Forall2 (WellInstantiated bck sub) xs ys ->
      (preserving_sub bck sub xs (anon_streams ys) (map fst xs) /\
       Forall (wc_clock (vars'++anon_streams ys)) (map fst ys)).
  Proof with eauto.
    intros vars' bck sub xs ys Hndup Hdep Hbck Hwc Hwinst.
    induction Hwinst; simpl.
    - rewrite app_nil_r. unfold preserving_sub...
    - assert (wc_env l) as Hwc' by (eapply wc_env_dep_ordered_on_remove in Hwc; eauto).
      simpl in Hdep. inv Hdep.
      inv Hndup.
      specialize (IHHwinst H5 H2 Hwc') as [Hpres' Hwc''].
      assert (preserving_sub bck sub ((a, b)::l) (anon_streams (y::l')) (map fst ((a, b)::l))) as Hpres''.
      { constructor; simpl in *; auto.
        - intros id' ck ck' Hsub Hinst Hin.
          inv Hin. 2:(apply In_InMembers in H0; congruence).
          inv H0. destruct y as [ck'' ?]. destruct H as [? Hinst']; simpl in *; subst.
          rewrite Hsub.
          left. f_equal; congruence.
        - eapply Forall_impl; [|eauto].
          intros id' Hin id'' ck' ck'' Hsub Hinst Hin'; simpl in *.
          destruct Hin' as [Heq|Hin'].
          + inv Heq.
             destruct y as [? ?]; destruct H as [Hsub' Hinst']; simpl in *.
             rewrite Hsub in Hsub'. rewrite Hinst in Hinst'. inv Hinst'.
             left...
          + specialize (Hin _ _ _ Hsub Hinst Hin').
             destruct y as [? [?|]]...
             right... }
      split; simpl...
      constructor; simpl.
      + destruct y as [ck [id|]]; simpl in *.
        * eapply WellInstantiated_wc_clock in H...
          -- inv Hwc...
          -- eapply wc_clock_incl...
             apply incl_appl, incl_refl.
          -- eapply preserving_sub_incl3. 1:eapply incl_tl, only_depends_on_frees_in_clock...
             eapply preserving_sub_incl2... apply incl_appr, incl_refl.
        * eapply WellInstantiated_wc_clock in H...
          -- inv Hwc...
          -- eapply wc_clock_incl...
             apply incl_appl, incl_refl.
          -- eapply preserving_sub_incl3. 1:eapply incl_tl, only_depends_on_frees_in_clock...
             eapply preserving_sub_incl2... apply incl_appr, incl_refl.
      + eapply Forall_impl; [|eauto].
        intros. eapply wc_clock_incl; eauto.
        apply incl_appr'.
        destruct y as [ck [id|]]; [apply incl_tl|]; apply incl_refl.
  Qed.

  Corollary WellInstantiated_wc_clocks : forall vars' bck sub xs ys,
      NoDupMembers xs ->
      wc_clock vars' bck ->
      wc_env xs ->
      Forall2 (WellInstantiated bck sub) xs ys ->
      Forall (wc_clock (vars'++anon_streams ys)) (map fst ys).
  Proof with eauto.
    intros vars' bck sub xs ys Hndup Hwc Hwenv Hwellinst.
    specialize (wc_env_dep_ordered_on _ Hndup Hwenv) as [xs' [Hperm1 Hdep1]].
    assert (NoDupMembers xs') as Hndup'' by (rewrite <- Hperm1; eauto).
    eapply Forall2_Permutation_1 in Hwellinst as [ys' [Hperm2 Hwellinst]]...
    eapply WellInstantiated_wc_clocks' in Hwellinst as (_&?);
      try rewrite app_nil_r in *; simpl in *...
    - eapply Forall_impl. 2:rewrite Hperm2...
      intros. unfold anon_streams. rewrite Hperm2...
    - rewrite <- Hperm1. assumption.
  Qed.

  Lemma wc_exp_clockof {prefs} : forall (G: @global prefs) vars e,
      wc_global G ->
      wc_env vars ->
      wc_exp G vars e ->
      Forall (wc_clock (vars++idck (fresh_in e))) (clockof e).
  Proof with eauto.
    Local Ltac Forall_clocksof :=
      match goal with
      | |- Forall _ (clocksof ?es) =>
        replace (clocksof es) with (concat (map clockof es))
          by (unfold clocksof; rewrite flat_map_concat_map; auto)
      end;
      apply Forall_concat; rewrite Forall_map;
      rewrite Forall_forall in *; intros ? Hin; eauto.

    intros G vars e HG Henv.
    induction e using exp_ind2; intros Hwc; inv Hwc;
      simpl; unfold clock_of_nclock, stripname; simpl; repeat constructor.
    - (* var *)
      simpl_list.
      unfold wc_env in Henv; rewrite Forall_forall in Henv.
      apply Henv in H0...
    - (* var (anon) *)
      simpl_list.
      unfold wc_env in Henv; rewrite Forall_forall in Henv.
      apply Henv in H0...
    - (* unop *)
      apply IHe in H1...
      rewrite H3 in H1. inv H1...
    - (* binop *)
      apply IHe1 in H3...
      rewrite H5 in H3. inv H3. clear H2.
      eapply wc_clock_incl; eauto.
      eapply incl_appr', incl_map, incl_appl, incl_refl.
    - (* fby *)
      rewrite Forall2_eq in H9, H10. unfold clock_of_nclock, stripname in H9; rewrite H9.
      Forall_clocksof...
      specialize (H _ Hin (H6 _ Hin)). rewrite Forall_forall in *; intros.
        apply H in H2. eapply wc_clock_incl; eauto. eapply incl_appr', incl_map, incl_appl, fresh_in_incl, Hin.
    - (* arrow *)
      rewrite Forall2_eq in H9, H10. unfold clock_of_nclock, stripname in H9; rewrite H9.
      Forall_clocksof...
      specialize (H _ Hin (H6 _ Hin)). rewrite Forall_forall in *; intros.
        apply H in H2. eapply wc_clock_incl; eauto. eapply incl_appr', incl_map, incl_appl, fresh_in_incl, Hin.
    - (* when *)
      destruct tys; [simpl in *; auto|].
      rewrite Forall_map. eapply Forall_forall; intros ? _.
      constructor. 2:eapply in_or_app...
      assert (Forall (wc_clock (vars++idck (fresh_ins es))) (clocksof es)) as Hwc.
      { Forall_clocksof.
        specialize (H _ Hin (H5 _ Hin)). rewrite Forall_forall in *; intros.
        apply H in H0. eapply wc_clock_incl; eauto. eapply incl_appr', incl_map, fresh_in_incl, Hin.
      } clear H.
      eapply Forall_Forall in H6...
      destruct (clocksof es); simpl in *; try congruence.
      inv H6. destruct H1; subst...
    - (* merge *)
      destruct es; [simpl in *; auto|]; try congruence.
      inv H. inv H5. simpl in H6; inv H6.
      assert (Forall (wc_clock (vars++idck (fresh_ins l))) (clocksof l)) as Hwc.
      { Forall_clocksof.
        specialize (H2 _ Hin (H1 _ Hin)). rewrite Forall_forall in *; intros.
        eapply wc_clock_incl; eauto. eapply incl_appr', incl_map, fresh_in_incl, Hin.
      } clear H2.
      eapply Forall_Forall in H10...
      inv H7. destruct (clocksof l).
      1:destruct tys; simpl in *; auto; try congruence.
      rewrite Forall_map. eapply Forall_forall; intros ? _.
      inv H10. destruct H6; subst. inv H.
      eapply wc_clock_incl... apply incl_appr', incl_map, incl_appl, incl_refl.
    - (* case *)
      apply IHe in H5. rewrite H6 in H5. apply Forall_singl in H5.
      rewrite Forall_map. eapply Forall_forall; intros ? _.
      eapply wc_clock_incl... apply incl_appr', incl_map, incl_appl, incl_refl.
    - (* app *)
      assert (Forall (wc_clock (vars++idck (fresh_ins es))) (clocksof es)) as Hwc.
      { Forall_clocksof.
        specialize (H _ Hin (H5 _ Hin)). rewrite Forall_forall in *; intros.
        apply H in H1. eapply wc_clock_incl; eauto. eapply incl_appr', incl_map, fresh_in_incl, Hin.
      } clear H.
      eapply wc_find_node in H7 as [G' Hwcnode]...
      assert (wc_clock (vars ++ idck (fresh_ins es)) bck) as Hbck.
      { eapply WellInstantiated_bck in H8...
        + rewrite <- clocksof_nclocksof in H8.
          rewrite Forall_forall in Hwc. apply Hwc in H8...
        + destruct Hwcnode as [? _]...
        + unfold idck. rewrite map_length. apply n_ingt0... }
      specialize (Forall2_app H8 H9) as Hinst.
      eapply WellInstantiated_wc_clocks in Hinst...
      + rewrite map_app, map_map, Forall_app in Hinst. destruct Hinst as [_ Hinst].
        eapply Forall_impl; [|eauto].
        intros; simpl in *. eapply wc_clock_incl...
        unfold anon_streams; rewrite map_filter_app.
        repeat rewrite <- app_assoc. repeat apply incl_app.
        * apply incl_appl, incl_refl.
        * apply incl_appr, incl_map, incl_appl, incl_refl.
        * etransitivity. eapply anon_streams_nclocksof_fresh_ins...
          apply incl_appr', incl_map, incl_appl, incl_refl.
        * unfold idck; repeat rewrite map_app.
          apply incl_appr, incl_appr, incl_appr. rewrite anon_streams_anon_streams.
          reflexivity.
      + specialize (n_nodup n) as Hndup.
        repeat rewrite app_assoc in Hndup. eapply NoDupMembers_app_l in Hndup.
        rewrite <- app_assoc, <- Permutation_swap in Hndup. eapply NoDupMembers_app_r in Hndup.
        rewrite fst_NoDupMembers in Hndup. rewrite fst_NoDupMembers.
        unfold idck. rewrite map_app in *. repeat rewrite map_map; simpl...
      + destruct Hwcnode as [_ [Hwcnode _]].
        unfold idck in *. rewrite map_app in Hwcnode...
  Qed.

  Corollary wc_exp_clocksof {prefs} : forall (G: @global prefs) vars es,
      wc_global G ->
      wc_env vars ->
      Forall (wc_exp G vars) es ->
      Forall (wc_clock (vars++idck (fresh_ins es))) (clocksof es).
  Proof with eauto.
    intros G vars es HwG Hwenv Hwc.
    induction Hwc; simpl. constructor.
    - eapply Forall_app. split.
      + eapply wc_exp_clockof in H...
        eapply Forall_impl; [|eauto]. intros.
        eapply wc_clock_incl; [|eauto].
        unfold fresh_ins, idck. simpl; rewrite map_app.
        apply incl_appr', incl_appl, incl_refl.
      + eapply Forall_impl; [|eauto]. intros.
        eapply wc_clock_incl; [|eauto].
        unfold fresh_ins, idck. simpl; rewrite map_app.
        apply incl_appr', incl_appr, incl_refl.
  Qed.

  Lemma wc_clock_is_free_in : forall vars ck,
      wc_clock vars ck ->
      forall x, Is_free_in_clock x ck -> InMembers x vars.
  Proof.
    intros * Hwc ? Hfree.
    induction Hwc; inv Hfree; eauto using In_InMembers.
  Qed.

  Corollary Forall_wc_clock_is_free_in : forall vars cks,
      Forall (wc_clock vars) cks ->
      Forall (fun ck => forall x, Is_free_in_clock x ck -> InMembers x vars) cks.
  Proof.
    intros * Hwcs.
    eapply Forall_impl; eauto.
    intros ck Hwc. eapply wc_clock_is_free_in; eauto.
  Qed.

  Corollary wc_env_is_free_in : forall vars,
      wc_env vars ->
      Forall (fun '(_, ck) => forall x, Is_free_in_clock x ck -> InMembers x vars) vars.
  Proof.
    intros * Hwenv. unfold wc_env in Hwenv.
    eapply Forall_impl; eauto.
    intros [? ck] Hwc. eapply wc_clock_is_free_in; eauto.
  Qed.

  Inductive dep_ordered_on' : list ident -> list nclock -> Prop :=
  | dep_ordered'_nil : forall vars, dep_ordered_on' vars []
  | dep_ordered'_cons : forall vars ncks ck name,
      dep_ordered_on' vars ncks ->
      only_depends_on (vars++map fst (anon_streams ncks)) ck ->
      dep_ordered_on' vars ((ck, name)::ncks).

  Fact dep_ordered_on'_Forall : forall vars ncks,
      dep_ordered_on' vars ncks ->
      Forall (fun '(ck, _) => only_depends_on (vars++map fst (anon_streams ncks)) ck) ncks.
  Proof.
    intros * Hdep; induction Hdep; constructor.
    - destruct name; simpl; auto.
      eapply only_depends_on_incl; eauto.
      apply incl_appr', incl_tl, incl_refl.
    - destruct name; simpl; auto.
      eapply Forall_impl; eauto.
      intros [ck' name'] Hdep'.
      eapply only_depends_on_incl; eauto.
      apply incl_appr', incl_tl, incl_refl.
  Qed.

  Lemma WellInstantiated_dep_ordered_on : forall bck bckinputs sub cks ncks,
      dep_ordered_on cks ->
      only_depends_on bckinputs bck ->
      Forall2 (WellInstantiated bck sub) cks ncks ->
      dep_ordered_on' bckinputs ncks.
  Proof.
    induction cks; intros * Hdep Hbck Hwi; inv Hdep; inv Hwi; simpl; try constructor.
    destruct y as [ck name].
    constructor; auto; simpl.
    erewrite <- WellInstantiated_sub_fsts; eauto.
    inv H3; simpl in *. eapply instck_only_depends_on in H0; eauto.
  Qed.

  Lemma WellInstantiated_is_free_in {prefs} : forall (G: @global prefs) f n inputs ins outs sub bck,
      wc_global G ->
      find_node f G = Some n ->
      Forall (fun '(ck, _) => forall x, Is_free_in_clock x ck -> In x inputs) ins ->
      Forall2 (WellInstantiated bck sub) (idck (n_in n)) ins ->
      Forall2 (WellInstantiated bck sub) (idck (n_out n)) outs ->
      Forall (fun '(ck, _) => forall x, Is_free_in_clock x ck ->
                                In x inputs \/
                                In x (map fst (anon_streams ins)) \/
                                In x (map fst (anon_streams outs))) outs.
  Proof.
    intros * HwcG Hfind Hinputs Hwi1 Hwi2.
    eapply wc_find_node in HwcG as [? Hwnode]; eauto.

    assert (In bck (map stripname ins)) as Hbck.
    { eapply WellInstantiated_bck in Hwi1; eauto.
      - destruct Hwnode as [? _]; eauto.
      - rewrite length_idck. exact (n_ingt0 n). }

    specialize (Forall2_app Hwi1 Hwi2) as Hwi. clear Hwi1 Hwi2.
    rewrite <- idck_app in Hwi.

    assert (exists vars, Permutation (idck (n_in n ++ n_out n)) vars /\ dep_ordered_on vars) as [vars [Hperm Hdepo]].
    { eapply wc_env_dep_ordered_on.
      - specialize (n_nodup n) as Hndup.
        rewrite NoDupMembers_idck.
        rewrite (Permutation_app_comm (n_vars n)), <- app_assoc, app_assoc in Hndup.
        apply NoDupMembers_app_l in Hndup; auto.
      - destruct Hwnode as [_ [? _]]; auto. }
    eapply Forall2_Permutation_1 in Hwi as [vars' [Hperm' Hwi]]; eauto.

    eapply WellInstantiated_dep_ordered_on with (bckinputs:=inputs) in Hwi; eauto.
    - apply dep_ordered_on'_Forall in Hwi.
      rewrite <- Hperm', Forall_app in Hwi. destruct Hwi as [_ ?].
      eapply Forall_impl; eauto. intros [ck ?] Hondep ? Hfree.
      eapply Hondep in Hfree. unfold anon_streams in Hfree; rewrite <- Hperm' in Hfree.
      rewrite map_filter_app, map_app in Hfree.
      repeat rewrite in_app_iff in Hfree; auto.
    - apply in_map_iff in Hbck as [[? ?] [? Hbck]]; subst.
      eapply Forall_forall in Hbck; eauto; simpl in *; auto.
  Qed.

  Section interface_eq.
    Context {prefs1 prefs2 : PS.t}.
    Variable G1 : @global prefs1.
    Variable G2 : @global prefs2.

    Hypothesis Heq : global_iface_eq G1 G2.

    Hint Constructors wc_exp.
    Fact iface_eq_wc_exp : forall vars e,
        wc_exp G1 vars e ->
        wc_exp G2 vars e.
    Proof with eauto.
      induction e using exp_ind2; intros Hwc; inv Hwc...
      1-5:econstructor; try (destruct Heq; erewrite <-equiv_program_enums)...
      1-10:rewrite Forall_forall in *...
      - intros ? Hin. specialize (H5 _ Hin). specialize (H _ Hin).
        rewrite Forall_forall in *...
      - intros ? Hin. specialize (H8 _ Hin). specialize (H _ Hin); simpl in H.
        rewrite Forall_forall in *...
      - (* app *)
        assert (Forall (wc_exp G2 vars) es) as Hwt by (rewrite Forall_forall in *; eauto).
        assert (Forall (wc_exp G2 vars) er) as Hwt' by (rewrite Forall_forall in *; eauto).
        destruct Heq as (Hequiv&Heq'). specialize (Heq' f).
        remember (find_node f G2) as find.
        destruct Heq'.
        + congruence.
        + inv H7.
          destruct H1 as [? [? [? ?]]].
          eapply wc_Eapp with (n0:=sy)...
          * rewrite <-H3...
          * rewrite <-H4...
    Qed.

    Fact iface_eq_wc_equation : forall vars equ,
        wc_equation G1 vars equ ->
        wc_equation G2 vars equ.
    Proof.
      intros vars [xs es] Hwc.
      simpl in *. destruct Hwc as [Hwc1 [Hwc2 Hwc3]].
      repeat split; auto.
      rewrite Forall_forall in *. intros x Hin.
      eapply iface_eq_wc_exp; eauto.
    Qed.

    (* Lemma iface_eq_wc_node : forall n, *)
    (*     wc_node G1 n -> *)
    (*     wc_node G2 n. *)
    (* Proof. *)
    (*   intros n Hwt. *)
    (*   destruct Hwt as [? [? [? Hwc]]]. *)
    (*   repeat split; auto. *)
    (*   rewrite Forall_forall in *; intros. *)
    (*   eapply iface_eq_wc_equation; eauto. *)
    (* Qed. *)

  End interface_eq.

  (** ** wc implies wl *)

  Hint Constructors wl_exp.
  Fact wc_exp_wl_exp {prefs} : forall (G: @global prefs) vars e,
      wc_exp G vars e ->
      wl_exp G e.
  Proof with eauto.
    induction e using exp_ind2; intro Hwt; inv Hwt; auto.
    - (* unop *)
      constructor...
      rewrite <- length_clockof_numstreams. rewrite H3. reflexivity.
    - (* binop *)
      constructor...
      + rewrite <- length_clockof_numstreams. rewrite H5. reflexivity.
      + rewrite <- length_clockof_numstreams. rewrite H6. reflexivity.
    - (* fby *)
      constructor; rewrite Forall_forall in *...
      + apply Forall2_length in H9. rewrite clocksof_annots in H9. repeat rewrite map_length in H9...
      + apply Forall2_length in H10. rewrite clocksof_annots in H10. repeat rewrite map_length in H10...
      + intros ? In. eapply H11 in In as (?&Ck). rewrite <- length_clockof_numstreams, Ck; auto.
    - (* arrow *)
      constructor; rewrite Forall_forall in *...
      + apply Forall2_length in H9. rewrite clocksof_annots in H9. repeat rewrite map_length in H9...
      + apply Forall2_length in H10. rewrite clocksof_annots in H10. repeat rewrite map_length in H10...
      + intros ? In. eapply H11 in In as (?&Ck). rewrite <- length_clockof_numstreams, Ck; auto.
    - (* when *)
      constructor; rewrite Forall_forall in *...
      rewrite clocksof_annots, map_length, map_length in H7...
    - (* merge *)
      constructor...
      + rewrite Forall_forall in *...
        intros ? Hin. specialize (H _ Hin). specialize (H5 _ Hin).
        rewrite Forall_forall in *...
      + rewrite Forall_forall in *...
        intros. erewrite H7; eauto.
        rewrite clocksof_annots, map_length, map_length...
    - (* case *)
      constructor...
      + rewrite <- length_clockof_numstreams, H6...
      + rewrite Forall_forall in *...
        intros ? Hin. specialize (H _ Hin); simpl in H. specialize (H8 _ Hin).
        rewrite Forall_forall in *...
      + rewrite Forall_forall in *...
        intros. erewrite H10; eauto.
        rewrite clocksof_annots, map_length, map_length...
      + rewrite Forall_forall in *...
      + rewrite clocksof_annots, map_length, map_length in H13...
    - (* app *)
      econstructor...
      + rewrite Forall_forall in *...
      + rewrite Forall_forall in *...
      + eapply Forall_impl; [|eauto]. intros ? (?&Ck).
        rewrite <- length_clockof_numstreams, Ck...
      + apply Forall2_length in H8. unfold idck in H8.
        rewrite nclocksof_annots in H8. repeat rewrite map_length in H8...
      + apply Forall2_length in H9. unfold idck in H9.
        repeat rewrite map_length in H9...
  Qed.
  Hint Resolve wc_exp_wl_exp.

  Corollary Forall_wc_exp_wl_exp {prefs} : forall (G: @global prefs) vars es,
      Forall (wc_exp G vars) es ->
      Forall (wl_exp G) es.
  Proof. intros. rewrite Forall_forall in *; eauto. Qed.
  Hint Resolve Forall_wc_exp_wl_exp.

  Fact wc_equation_wl_equation {prefs} : forall (G: @global prefs) vars equ,
      wc_equation G vars equ ->
      wl_equation G equ.
  Proof with eauto.
    intros G vars [xs es] [Hwc1 [Hwc2 _]].
    constructor.
    + rewrite Forall_forall in *...
    + rewrite nclocksof_annots in Hwc2.
      apply Forall2_length in Hwc2.
      rewrite map_length in Hwc2...
  Qed.
  Hint Resolve wc_equation_wl_equation.

  Fact wc_node_wl_node {prefs} : forall (G: @global prefs) n,
      wc_node G n ->
      wl_node G n.
  Proof with eauto.
    intros G n [_ [_ [_ Hwc]]].
    unfold wl_node.
    rewrite Forall_forall in *...
  Qed.
  Hint Resolve wc_node_wl_node.

  Fact wc_global_wl_global {prefs} : forall (G: @global prefs),
      wc_global G ->
      wl_global G.
  Proof with eauto.
    intros G Hwt.
    unfold wc_global, wl_global, wt_program in *.
    induction Hwt; constructor...
    destruct H...
  Qed.
  Hint Resolve wc_global_wl_global.

End LCLOCKING.

Module LClockingFun
       (Ids   : IDS)
       (Op    : OPERATORS)
       (OpAux : OPERATORS_AUX Ids Op)
       (Cks   : CLOCKS Ids Op OpAux)
       (Syn   : LSYNTAX Ids Op OpAux Cks)
       <: LCLOCKING Ids Op OpAux Cks Syn.
  Include LCLOCKING Ids Op OpAux Cks Syn.
End LClockingFun.
