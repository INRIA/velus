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

From Coq Require Import Program.Basics Program.Wf.
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

    (** EvarAnon is used at toplevel of an equation, to allow for equations of the form
        x = y, without having to specify a name. Evar is used internally to expressions *)
    Inductive wc_exp : exp -> Prop :=
    | wc_Econst: forall c,
        wc_exp (Econst c)

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

  Definition wc_equation (xses : equation) : Prop :=
    let (xs, es) := xses in
    Forall wc_exp es
    /\ Forall2 (fun x nc => LiftO True (eq x) (snd nc)) xs (nclocksof es)
    /\ Forall2 (fun x ck => In (x, ck) vars) xs (clocksof es).
  End WellClocked.

  Definition wc_node (G: global) (n: node) : Prop
    :=    wc_env (idck  n.(n_in))
       /\ wc_env (idck (n.(n_in) ++ n.(n_out)))
       /\ wc_env (idck (n.(n_in) ++ n.(n_out) ++ n.(n_vars)))
       /\ Forall (wc_equation G (idck (n.(n_in) ++ n.(n_vars) ++ n.(n_out)))) n.(n_eqs).

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

  Instance wc_equation_Proper:
    Proper (@eq global ==> @Permutation.Permutation (ident * clock)
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

    Function check_nclock (x : ident) (nck : nclock) : bool :=
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

        destruct ro;
          simpl in *; DestructMatch; subst;
            try match goal with H:check_exp ?e = Some [?nc] |- _ => destruct nc end;
            econstructor; eauto;
            take (forall ncks, Some _ = Some ncks -> _ /\ _) and rename it into CE;
            specialize (CE _ eq_refl) as (CE1 & CE2); eauto.
        now apply nclockof_clockof with (1:=CE2).
    Qed.

    Lemma oconcat_map_check_exp:
      forall es ncks,
        oconcat (map check_exp es) = Some ncks ->
        Forall (wc_exp G (idck (Env.elements venv))) es
        /\ nclocksof es = ncks.
    Proof.
      induction es as [|e es IH]; intros ncks CE. now inv CE; eauto.
      simpl in CE. DestructMatch.
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
        wc_equation G (idck (Env.elements venv)) eq.
    Proof.
      intros eq CE. destruct eq as (xs, es); simpl in CE.
      DestructMatch.
      take (oconcat (map _ _) = Some _)
      and apply oconcat_map_check_exp in it as (WC & NC).
      subst. apply forall2b_Forall2 in CE.
      constructor; auto.
      rewrite clocksof_nclocksof, Forall2_map_2.
      split; apply Forall2_impl_In with (2:=CE); intros x (ck, nm) Ix Inc CNC;
        simpl in *; DestructMatch;
        apply Bool.andb_true_iff in CNC as (CNC1 & CNC2);
        take (check_var _ _ = true) and apply check_var_correct in it;
        auto.
      destruct nm; simpl; auto.
      now rewrite equiv_decb_equiv in CNC2.
    Qed.

  End ValidateExpression.

  (** Adding variables to the environment preserves clocking *)

  Section incl.

    Fact wc_clock_incl : forall vars vars' cl,
      incl vars vars' ->
      wc_clock vars cl ->
      wc_clock vars' cl.
    Proof.
      intros vars vars' cl Hincl Hwc.
      induction Hwc; auto.
    Qed.

    Hint Constructors wc_exp.
    Fact wc_exp_incl : forall G vars vars' e,
        incl vars vars' ->
        wc_exp G vars e ->
        wc_exp G vars' e .
    Proof with eauto.
      induction e using exp_ind2; intros Hincl Hwc; inv Hwc; eauto;
        econstructor; rewrite Forall_forall in *; eauto.
    Qed.

    Fact wc_equation_incl : forall G vars vars' eq,
        incl vars vars' ->
        wc_equation G vars eq ->
        wc_equation G vars' eq.
    Proof with eauto.
      intros G vars vars' [xs es] Hincl Hwc.
      destruct Hwc as [? [? ?]].
      repeat split...
      - rewrite Forall_forall in *; intros.
        eapply wc_exp_incl...
      - clear H H0.
        eapply Forall2_impl_In; [| eauto].
        intros a b Hin1 Hin2 Hin; simpl in Hin. eapply Hincl...
    Qed.
  End incl.

  (** *** Some additional properties related to remove_member *)

  Definition remove_member {B} := @remove_member _ B EqDec_instance_0.

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

  (** The clock of a var cant depend on its var *)
  Lemma wc_nfree_in_clock : forall vars ck id,
      wc_env vars ->
      NoDupMembers vars ->
      In (id, ck) vars ->
      wc_clock vars ck ->
      ~Is_free_in_clock id ck.
  Proof.
    intros vars ck id Hwenv Hndup Hin Hwc contra.
    apply Is_free_in_clock_self_or_parent in contra as [ck' [b [H|H]]]; subst.
    - inv Hwc.
      eapply NoDupMembers_det in Hndup. 2:eapply H3. 2:eapply Hin.
      apply clock_not_in_clock in Hndup; auto.
    - assert (In (id, ck') vars) as Hin' by (eapply wc_clock_parent in H; eauto; inv H; eauto).
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
        specialize (remove_member_Perm EqDec_instance_0 _ _ _ Hndup Hin) as Hperm. symmetry in Hperm.
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
      destruct EqDec_instance_0 in Hwc; try congruence.
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
    inv Hndup; inv Hdep. simpl in *; constructor.
    - apply IHncks...
      eapply wc_env_nfreein_remove with (id:=id) in Hwc.
      + simpl in *. destruct EqDec_instance_0 in Hwc; try congruence.
        unfold remove_member in Hwc. rewrite remove_member_nIn_idem in Hwc...
      + constructor...
      + constructor.
        * eapply wc_nfree_in_clock in Hwc... 1,2:constructor...
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

  Lemma instck_only_depends_on : forall vars bck sub ck ck',
      only_depends_on (map_filter sub vars) bck ->
      only_depends_on vars ck ->
      instck bck sub ck = Some ck' ->
      only_depends_on (map_filter sub vars) ck'.
  Proof with eauto.
    induction ck; intros ck' Hbck Hdep Hinst; simpl in *.
    - inv Hinst...
    - destruct instck eqn:Hinst'; try congruence.
      destruct sub eqn:Hsub; try congruence.
      inv Hinst.
      specialize (only_depends_on_Con _ _ _ _ Hdep) as Hdep'.
      specialize (IHck _ Hbck Hdep' eq_refl).
      intros id Hfree. inv Hfree.
      + specialize (Hdep i (FreeCon1 _ _ _)).
        eapply map_filter_In; eauto.
      + apply IHck...
  Qed.

  (** *** Relation between nclocksof and fresh_ins *)

  Lemma anon_streams_nclockof_fresh_in : forall G vars e,
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
      2: { clear H H0 H4 H5 H6 H7.
           induction a; simpl; auto. inv H8.
           rewrite <- IHa... unfold unnamed_stream in H1.
           destruct a as [ty [ck id]]; simpl in *; subst. reflexivity. }
      apply incl_nil'.
    - (* when *)
      replace (anon_streams _) with (@nil (ident * clock)).
      2: { clear H H4 H5 H6 H7.
           induction tys; simpl; auto. }
      apply incl_nil'.
    - (* merge *)
      replace (anon_streams _) with (@nil (ident * clock)).
      2: { clear H H0 H5 H6 H7 H8 H9 H10 H11.
           induction tys; simpl; auto. }
      apply incl_nil'.
    - (* ite *)
      replace (anon_streams _) with (@nil (ident * clock)).
      2: { clear H H0 H5 H6 H7 H8 H9 H10 H11 H12 H13.
           induction tys; simpl; auto. }
      apply incl_nil'.
    - (* app *)
      unfold idck. rewrite map_app.
      apply incl_appr, incl_appr.
      rewrite anon_streams_anon_streams. reflexivity.
    - (* app *)
      unfold idck. repeat rewrite map_app.
      apply incl_appr, incl_appr, incl_appr.
      rewrite anon_streams_anon_streams. reflexivity.
  Qed.

  Corollary anon_streams_nclocksof_fresh_ins : forall G vars es,
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

  Fact fresh_in_incl : forall e es,
      In e es ->
      incl (fresh_in e) (fresh_ins es).
  Proof.
    intros e es Hin.
    unfold fresh_ins. apply concat_map_incl; auto.
  Qed.

  Fact anon_in_incl : forall e es,
      In e es ->
      incl (anon_in e) (anon_ins es).
  Proof.
    intros e es Hin.
    unfold anon_ins. apply concat_map_incl; auto.
  Qed.

  Fact anon_in_eq_incl : forall e es,
      In e es ->
      incl (anon_in_eq e) (anon_in_eqs es).
  Proof.
    intros e es Hin.
    unfold anon_in_eqs. apply concat_map_incl; auto.
  Qed.

  Lemma wc_exp_clockof : forall G vars e,
      wc_global G ->
      wc_env vars ->
      wc_exp G vars e ->
      Forall (wc_clock (vars++idck (fresh_in e))) (clockof e).
  Proof with eauto.
    Local Ltac Forall_clocksof :=
      unfold clocksof; rewrite flat_map_concat_map;
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
      rewrite Forall2_eq in H6, H7. unfold clock_of_nclock, stripname in H6; rewrite H6.
      Forall_clocksof...
      specialize (H _ Hin (H4 _ Hin)). rewrite Forall_forall in *; intros.
        apply H in H1. eapply wc_clock_incl; eauto. eapply incl_appr', incl_map, incl_appl, fresh_in_incl, Hin.
    - (* when *)
      destruct tys; [simpl in *; auto|].
      rewrite Forall_map. eapply Forall_forall; intros ? _.
      constructor. 2:eapply in_or_app...
      assert (Forall (wc_clock (vars++idck (fresh_ins es))) (clocksof es)) as Hwc.
      { Forall_clocksof.
        specialize (H _ Hin (H4 _ Hin)). rewrite Forall_forall in *; intros.
        apply H in H0. eapply wc_clock_incl; eauto. eapply incl_appr', incl_map, fresh_in_incl, Hin.
      } clear H.
      eapply Forall_Forall in H6...
      destruct (clocksof es); simpl in *; try congruence.
      inv H6. destruct H1; subst...
    - (* merge *)
      destruct tys; [simpl in *; auto|].
      rewrite Forall_map. eapply Forall_forall; intros ? _.
      assert (Forall (wc_clock (vars++idck (fresh_ins ets))) (clocksof ets)) as Hwc.
      { Forall_clocksof.
        specialize (H _ Hin (H5 _ Hin)). rewrite Forall_forall in *; intros.
        apply H in H1. eapply wc_clock_incl; eauto. eapply incl_appr', incl_map, fresh_in_incl, Hin.
      } clear H.
      eapply Forall_Forall in H8...
      destruct (clocksof ets); simpl in *; try congruence.
      inv H8. destruct H2; subst. inv H.
      eapply wc_clock_incl... apply incl_appr', incl_map, incl_appl, incl_refl.
    - (* ite *)
      destruct tys; [simpl in *; auto|].
      rewrite Forall_map. eapply Forall_forall; intros ? _.
      assert (Forall (wc_clock (vars++idck (fresh_ins ets))) (clocksof ets)) as Hwc.
      { Forall_clocksof.
        specialize (H _ Hin (H6 _ Hin)). rewrite Forall_forall in *; intros.
        apply H in H1. eapply wc_clock_incl; eauto. eapply incl_appr', incl_map, fresh_in_incl, Hin.
      } clear H.
      eapply Forall_Forall in H9...
      destruct (clocksof ets); simpl in *; try congruence.
      inv H9. destruct H2; subst.
      eapply wc_clock_incl... apply incl_appr', incl_map, incl_appr, incl_appl, incl_refl.
    - (* app *)
      assert (Forall (wc_clock (vars++idck (fresh_ins es))) (clocksof es)) as Hwc.
      { Forall_clocksof.
        specialize (H0 _ Hin (H5 _ Hin)). rewrite Forall_forall in *; intros.
        apply H0 in H1. eapply wc_clock_incl; eauto. eapply incl_appr', incl_map, fresh_in_incl, Hin.
      } clear H.
      eapply wc_find_node in H6 as [G' Hwcnode]...
      assert (wc_clock (vars ++ idck (fresh_ins es)) bck) as Hbck.
      { eapply WellInstantiated_bck in H7...
        + rewrite <- clocksof_nclocksof in H7.
          rewrite Forall_forall in Hwc. apply Hwc in H7...
        + destruct Hwcnode as [? _]...
        + unfold idck. rewrite map_length. apply n_ingt0... }
      specialize (Forall2_app H7 H8) as Hinst.
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
        * unfold idck; rewrite map_app.
          apply incl_appr, incl_appr. rewrite anon_streams_anon_streams.
          reflexivity.
      + specialize (n_nodup n) as Hndup.
        repeat rewrite app_assoc in Hndup. eapply NoDupMembers_app_l in Hndup.
        rewrite <- app_assoc, <- Permutation_swap in Hndup. eapply NoDupMembers_app_r in Hndup.
        rewrite fst_NoDupMembers in Hndup. rewrite fst_NoDupMembers.
        unfold idck. rewrite map_app in *. repeat rewrite map_map; simpl...
      + destruct Hwcnode as [_ [Hwcnode _]].
        unfold idck in *. rewrite map_app in Hwcnode...
    - (* app (reset) *)
      assert (Forall (wc_clock (vars++idck (fresh_ins es))) (clocksof es)) as Hwc.
      { Forall_clocksof.
        specialize (H0 _ Hin (H5 _ Hin)). rewrite Forall_forall in *; intros.
        apply H0 in H1. eapply wc_clock_incl; eauto. eapply incl_appr', incl_map, fresh_in_incl, Hin.
      } clear H.
      eapply wc_find_node in H6 as [G' Hwcnode]...
      assert (wc_clock (vars ++ idck (fresh_ins es)) bck) as Hbck.
      { eapply WellInstantiated_bck in H7...
        + rewrite <- clocksof_nclocksof in H7.
          rewrite Forall_forall in Hwc. apply Hwc in H7...
        + destruct Hwcnode as [? _]...
        + unfold idck. rewrite map_length. apply n_ingt0... }
      specialize (Forall2_app H7 H8) as Hinst.
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

  Corollary wc_exp_clocksof : forall G vars es,
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

  Section interface_eq.

    Hint Constructors wc_exp.
    Fact iface_eq_wc_exp : forall G G' vars e,
        global_iface_eq G G' ->
        wc_exp G vars e ->
        wc_exp G' vars e.
    Proof with eauto.
      induction e using exp_ind2; intros Heq Hwt; inv Hwt...
      - (* fby *)
        econstructor...
        + rewrite Forall_forall in *...
        + rewrite Forall_forall in *...
      - (* when *)
        econstructor...
        rewrite Forall_forall in *...
      - (* merge *)
        econstructor...
        + rewrite Forall_forall in *...
        + rewrite Forall_forall in *...
      - (* ite *)
        econstructor...
        + rewrite Forall_forall in *...
        + rewrite Forall_forall in *...
      - (* app *)
        assert (Forall (wc_exp G' vars) es) as Hwt by (rewrite Forall_forall in *; eauto).
        specialize (Heq f).
        remember (find_node f G') as find.
        destruct Heq.
        + congruence.
        + inv H6.
          destruct H1 as [? [? [? ?]]].
          eapply wc_Eapp with (n:=sy)...
          * rewrite <- H3...
          * rewrite <- H4...
      - (* app (reset) *)
        assert (Forall (wc_exp G' vars) es) as Hwt by (rewrite Forall_forall in *; eauto).
        assert (wc_exp G' vars r) as Hwt' by (rewrite Forall_forall in *; eauto).
        specialize (Heq f).
        remember (find_node f G') as find.
        destruct Heq.
        + congruence.
        + inv H6.
          destruct H1 as [? [? [? ?]]].
          eapply wc_EappReset with (n:=sy)...
          * rewrite <- H3...
          * rewrite <- H4...
    Qed.

    Fact iface_eq_wc_equation : forall G G' vars equ,
        global_iface_eq G G' ->
        wc_equation G vars equ ->
        wc_equation G' vars equ.
    Proof.
      intros G G' vars [xs es] Heq Hwc.
      simpl in *. destruct Hwc as [Hwc1 [Hwc2 Hwc3]].
      repeat split; auto.
      rewrite Forall_forall in *. intros x Hin.
      eapply iface_eq_wc_exp; eauto.
    Qed.

    Lemma iface_eq_wc_node : forall G G' n,
        global_iface_eq G G' ->
        wc_node G n ->
        wc_node G' n.
    Proof.
      intros G G' n Heq Hwt.
      destruct Hwt as [? [? [? Hwc]]].
      repeat split; auto.
      rewrite Forall_forall in *; intros.
      eapply iface_eq_wc_equation; eauto.
    Qed.

  End interface_eq.

  (** ** wc implies wl *)

  Hint Constructors wl_exp.
  Fact wc_exp_wl_exp : forall G vars e,
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
      + apply Forall2_length in H6. rewrite clocksof_annots in H6. repeat rewrite map_length in H6...
      + apply Forall2_length in H7. rewrite clocksof_annots in H7. repeat rewrite map_length in H7...
    - (* when *)
      constructor; rewrite Forall_forall in *...
      rewrite clocksof_annots, map_length, map_length in H7...
    - (* merge *)
      constructor; rewrite Forall_forall in *...
      + rewrite clocksof_annots, map_length, map_length in H10...
      + rewrite clocksof_annots, map_length, map_length in H11...
    - (* ite *)
      constructor; rewrite Forall_forall in *...
      + rewrite <- length_clockof_numstreams, H8. reflexivity.
      + rewrite clocksof_annots, map_length, map_length in H11...
      + rewrite clocksof_annots, map_length, map_length in H12...
    - (* app *)
      econstructor...
      + rewrite Forall_forall in *...
      + apply Forall2_length in H7. unfold idck in H7.
        rewrite nclocksof_annots in H7. repeat rewrite map_length in H7...
      + apply Forall2_length in H8. unfold idck in H8.
        repeat rewrite map_length in H8...
    - (* app (reset) *)
      econstructor...
      + rewrite Forall_forall in *...
      + rewrite <- length_clockof_numstreams, H10...
      + apply Forall2_length in H7. unfold idck in H7.
        rewrite nclocksof_annots in H7. repeat rewrite map_length in H7...
      + apply Forall2_length in H8. unfold idck in H8.
        repeat rewrite map_length in H8...
  Qed.
  Hint Resolve wc_exp_wl_exp.

  Corollary Forall_wc_exp_wl_exp : forall G vars es,
      Forall (wc_exp G vars) es ->
      Forall (wl_exp G) es.
  Proof. intros. rewrite Forall_forall in *; eauto. Qed.
  Hint Resolve Forall_wc_exp_wl_exp.

  Fact wc_equation_wl_equation : forall G vars equ,
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

  Fact wc_node_wl_node : forall G n,
      wc_node G n ->
      wl_node G n.
  Proof with eauto.
    intros G n [_ [_ [_ Hwc]]].
    unfold wl_node.
    rewrite Forall_forall in *...
  Qed.
  Hint Resolve wc_node_wl_node.

  Fact wc_global_wl_global : forall G,
      wc_global G ->
      wl_global G.
  Proof with eauto.
    intros G Hwt.
    induction Hwt; constructor...
  Qed.
  Hint Resolve wc_global_wl_global.
End LCLOCKING.

Module LClockingFun
       (Ids  : IDS)
       (Op   : OPERATORS)
       (Syn  : LSYNTAX Ids Op)
       <: LCLOCKING Ids Op Syn.
  Include LCLOCKING Ids Op Syn.
End LClockingFun.
