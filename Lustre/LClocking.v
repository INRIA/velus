Require Import Velus.Common.
Require Import Velus.Operators.
Require Import Velus.Clocks.
Require Import LSyntax.

Require Import List.
Import List.ListNotations.
Open Scope list_scope.

Require Import Morphisms.
Import Permutation.

(** * Lustre typing *)

(**

  Clocking judgements for Lustre.
  Classify Lustre programs which are statically well-formed.

 *)

Module Type LCLOCKING
       (Import Ids  : IDS)
       (Import Op   : OPERATORS)
       (Import Syn  : LSYNTAX Ids Op).

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

  (* input substitution (universal elimination):
     parameter names may be replaced by either fresh or named clocks.  *)
  Definition imap := ident -> option ckid.

  (* output substituition (existential introduction):
     parameter names may only be replaced by fresh clocks. *)
  Definition omap := ident -> option positive.

  (* pattern substitution: unify fresh clocks with variables. *)
  Definition pmap := positive -> option ident.

  (* instantiate the parameter names in a clock, giving a stream clock *)
  Fixpoint sinst (base: sclock) (subst: imap) (ck: clock) : option sclock :=
    match ck with
    | Cbase => Some base
    | Con ck x b =>
      match sinst base subst ck, subst x with
      | Some ck', Some x' => Some (Son ck' x' b)
      | _, _ => None
      end
    end.

  (* instantiate a parameter, giving a named clock *)
  Definition inst (b: sclock) (sub: imap)
                  (xtc: ident * (type * clock)) : option nclock :=
    let '(x, (ty, ck)) := xtc in
    match sinst b sub ck with
    | None => None
    | Some ck' => match sub x with
                  | None => Some (Cstream ck')
                  | Some ni => Some (Cnamed ni ck')
                  end
    end.

  (* instantiate an input parameter, giving a named clock *)
  Definition inst_in (b: sclock) (isub: Env.t ckid)
                     : (ident * (type * clock)) -> option nclock :=
    inst b (fun x => Env.find x isub).

  (* instantiate an output parameter, giving a named clock *)
  Definition inst_out (b: sclock) (osub: Env.t positive) (isub: Env.t ckid)
                      : (ident * (type * clock)) -> option nclock :=
    inst b (fun x=>match Env.find x osub with
                   | Some i => Some (Vidx i)
                   | None   => Env.find x isub
                   end).

  (* Instantiate the fresh clocks in a stream clock, giving a clock or None
     if fresh clocks would 'escape'. *)

  Definition pninst (sub: pmap) (ni: ckid) : option ident :=
    match ni with
    | Vnm x => Some x
    | Vidx i => sub i
    end.

  Fixpoint pinst (sub: pmap) (sck: sclock) : option clock :=
    match sck with
    | Sbase => Some Cbase
    | Son sck' ni b =>
      match pinst sub sck', pninst sub ni with
      | Some ck', Some x => Some (Con ck' x b)
      | _, _ => None
      end
    end.

  Definition patsub (ncs: list nclock) (xs: list ident)
                    (i: positive) : option ident :=
    option_map snd (find (fun nx=> match fst nx with
                                   | Cnamed (Vidx j) _ => Pos.eqb i j
                                   | _ => false
                                   end) (combine ncs xs)).

  Section WellClocked.

    Variable G    : global.
    Variable vars : list (ident * clock).

    Inductive wc_exp : exp -> Prop :=
    | wc_Econst: forall c,
        wc_exp (Econst c)

    | wc_Evar: forall x ty ck,
        In (x, ck) vars ->
        wc_exp (Evar x (ty, Cnamed (Vnm x) (sclk ck)))

    | wc_Eunop: forall op e ty ck,
        wc_exp e ->
        clockof e = [ck] ->
        wc_exp (Eunop op e (ty, Cstream ck))

    | wc_Ebinop: forall op e1 e2 ty ck,
        wc_exp e1 ->
        wc_exp e2 ->
        clockof e1 = [ck] ->
        clockof e2 = [ck] ->
        wc_exp (Ebinop op e1 e2 (ty, Cstream ck))

    | wc_Efby: forall e0s es anns,
        Forall wc_exp e0s ->
        Forall wc_exp es ->
        Forall2 eq (map ckstream anns) (clocksof e0s) ->
        Forall2 eq (map ckstream anns) (clocksof es) ->
        Forall is_ckstream anns ->
        wc_exp (Efby e0s es anns)

    | wc_Ewhen: forall es x b tys ck,
        Forall wc_exp es ->
        In (x, ck) vars ->
        Forall (eq (sclk ck)) (clocksof es) ->
        wc_exp (Ewhen es x b (tys, Cstream (Son (sclk ck) (Vnm x) b)))

    | wc_Emerge: forall x ets efs tys ck,
        Forall wc_exp ets ->
        Forall wc_exp efs ->
        In (x, ck) vars ->
        Forall (eq (Son (sclk ck) (Vnm x) true))  (clocksof ets) ->
        Forall (eq (Son (sclk ck) (Vnm x) false)) (clocksof efs) ->
        wc_exp (Emerge x ets efs (tys, Cstream (sclk ck)))

    | wc_Eifte: forall e ets efs tys ck,
        wc_exp e ->
        Forall wc_exp ets ->
        Forall wc_exp efs ->
        clockof e = [ck] ->
        Forall (eq ck) (clocksof ets) ->
        Forall (eq ck) (clocksof efs) ->
        wc_exp (Eite e ets efs (tys, Cstream ck))

    | wc_Eapp: forall f es anns n,
        Forall wc_exp es ->
        DisjointIndexes (map nclockof es) ->
        NoDup (indexes (map snd anns)) ->
        find_node f G = Some n ->
        (exists b isub osub,
            Forall2 (fun xtc cke => inst_in b isub xtc = Some cke)
                    n.(n_in) (nclocksof es)
            /\ Forall2 (fun xtc a => inst_out b osub isub xtc = Some (snd a))
                       n.(n_out) anns) ->
        wc_exp (Eapp f es anns).

    Definition wc_patvar (pvars: list ident) (ncks: list nclock)
                         (x: ident) (sck: sclock) : Prop :=
      match pinst (patsub ncks pvars) sck with
      | Some ck => In (x, ck) vars
      | None => False
      end.

    Definition wc_equation (eq : equation) : Prop :=
      let (xs, es) := eq in
      Forall wc_exp es
      /\ DisjointIndexes (map nclockof es)
      /\ Forall2 (wc_patvar xs (nclocksof es)) xs (clocksof es).

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
        P (Evar x (ty, Cnamed (Vnm x) (sclk ck))).

    Hypothesis EunopCase:
      forall op e ty ck,
        wc_exp G vars e ->
        P e ->
        clockof e = [ck] ->
        P (Eunop op e (ty, Cstream ck)).

    Hypothesis EbinopCase:
      forall op e1 e2 ty ck,
        wc_exp G vars e1 ->
        P e1 ->
        wc_exp G vars e2 ->
        P e2 ->
        clockof e1 = [ck] ->
        clockof e2 = [ck] ->
        P (Ebinop op e1 e2 (ty, Cstream ck)).

    Hypothesis EfbyCase:
      forall e0s es anns,
        Forall (wc_exp G vars) e0s ->
        Forall (wc_exp G vars) es ->
        Forall P es ->
        Forall P e0s ->
        Forall2 eq (map ckstream anns) (clocksof e0s) ->
        Forall2 eq (map ckstream anns) (clocksof es) ->
        Forall is_ckstream anns ->
        P (Efby e0s es anns).

    Hypothesis EwhenCase:
      forall es x b tys ck,
        Forall (wc_exp G vars) es ->
        Forall P es ->
        In (x, ck) vars ->
        Forall (eq (sclk ck)) (clocksof es) ->
        P (Ewhen es x b (tys, Cstream (Son (sclk ck) (Vnm x) b))).

    Hypothesis EmergeCase:
      forall x ets efs tys ck,
        Forall (wc_exp G vars) ets ->
        Forall P ets ->
        Forall (wc_exp G vars) efs ->
        Forall P efs ->
        In (x, ck) vars ->
        Forall (eq (Son (sclk ck) (Vnm x) true))  (clocksof ets) ->
        Forall (eq (Son (sclk ck) (Vnm x) false)) (clocksof efs) ->
        P (Emerge x ets efs (tys, Cstream (sclk ck))).

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
        P (Eite e ets efs (tys, Cstream ck)).

    Hypothesis EappCase:
      forall f es anns n,
        Forall (wc_exp G vars) es ->
        DisjointIndexes (map nclockof es) ->
        NoDup (indexes (map snd anns)) ->
        Forall P es ->
        find_node f G = Some n ->
        (exists b isub osub,
            Forall2 (fun xtc cke => inst_in b isub xtc = Some cke)
                    n.(n_in) (nclocksof es)
            /\ Forall2 (fun xtc a => inst_out b osub isub xtc = Some (snd a))
                       n.(n_out) anns) ->
        P (Eapp f es anns).

    Fixpoint wc_exp_ind2 (e: exp) (H: wc_exp G vars e) {struct H} : P e.
    Proof.
      destruct H; eauto.
      - apply EfbyCase; auto.
        + clear H2. induction H0; auto.
        + clear H1. induction H; auto.
      - apply EwhenCase; auto.
        clear H1. induction H; auto.
      - apply EmergeCase; auto.
        clear H2. induction H; auto.
        clear H3. induction H0; auto.
      - apply EiteCase; auto.
        clear H3. induction H0; auto.
        clear H4. induction H1; auto.
      - eapply EappCase; eauto.
        clear H0 H1 H2 H3. induction H; eauto.
    Qed.

  End wc_exp_ind2.

  Lemma wc_sclk:
    forall env ck,
      wc_clock env ck ->
      wc_sclock env (sclk ck).
  Proof.
    induction ck. now auto with lclocking.
    inversion_clear 1. simpl; eauto with lclocking.
  Qed.

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

  Lemma sinst_extarg:
    forall f g bck ck,
      (forall x, f x = g x) ->
      sinst bck f ck = sinst bck g ck.
  Proof.
    intros * Hext.
    induction ck; auto.
    simpl. now rewrite IHck, Hext.
  Qed.

  Lemma wc_NoDup_indexes:
    forall G env e,
      wc_exp G env e ->
      NoDup (indexes (nclockof e)).
  Proof.
    induction e; simpl.
    - auto using NoDup.
    - destruct a as (ty, nck); destruct nck.
      simpl; auto using NoDup.
      destruct c; simpl; auto using NoDup.
    - destruct a as (ty, nck); destruct nck.
      simpl; auto using NoDup.
      destruct c; simpl; auto using NoDup.
    - destruct a as (ty, nck); destruct nck.
      simpl; auto using NoDup.
      destruct c; simpl; auto using NoDup.
    - inversion_clear 1.
      rewrite is_ckstream_NoDup_indexes; auto using NoDup.
    - inversion_clear 1.
      induction tys; simpl; auto using NoDup.
    - inversion_clear 1.
      induction tys; simpl; auto using NoDup.
    - inversion_clear 1.
      induction tys; simpl; auto using NoDup.
    - now inversion_clear 1.
  Qed.

  Lemma indexes_app:
    forall xs ys,
      indexes (xs ++ ys) = indexes xs ++ indexes ys.
  Proof.
    induction xs as [|x xs IH]. reflexivity.
    destruct x; simpl; auto.
    destruct c; simpl; auto.
    now setoid_rewrite IH.
  Qed.

  Lemma indexes_Is_index_in_nclocks:
    forall i e,
      In i (indexes (nclockof e)) ->
      Is_index_in_nclocks i (nclockof e).
  Proof.
    intros * Hin. destruct e; simpl in *.
    - contradiction.
    - destruct a as (ty, nck). destruct nck; simpl in *.
      contradiction. destruct c; inversion_clear Hin; subst.
      now repeat constructor. now inv H.
    - destruct a as (ty, nck). destruct nck; simpl in *.
      contradiction. destruct c; inversion_clear Hin; subst.
      now repeat constructor. now inv H.
    - destruct a as (ty, nck). destruct nck; simpl in *.
      contradiction. destruct c; inversion_clear Hin; subst.
      now repeat constructor. now inv H.
    - match goal with |- Is_index_in_nclocks _ ?xs =>
        induction xs as [|nck anns IH] end. now inv Hin.
      destruct nck; simpl in *.
      now constructor 2; apply IH.
      destruct c. 2:now constructor 2; apply IH.
      inv Hin. now repeat constructor. now constructor 2; apply IH.
    - match goal with |- Is_index_in_nclocks _ ?xs =>
        induction xs as [|nck anns IH] end. now inv Hin.
      destruct nck; simpl in *.
      now constructor 2; apply IH.
      destruct c. 2:now constructor 2; apply IH.
      inv Hin. now repeat constructor. now constructor 2; apply IH.
    - match goal with |- Is_index_in_nclocks _ ?xs =>
        induction xs as [|nck anns IH] end. now inv Hin.
      destruct nck; simpl in *.
      now constructor 2; apply IH.
      destruct c. 2:now constructor 2; apply IH.
      inv Hin. now repeat constructor. now constructor 2; apply IH.
    - match goal with |- Is_index_in_nclocks _ ?xs =>
        induction xs as [|nck anns IH] end. now inv Hin.
      destruct nck; simpl in *.
      now constructor 2; apply IH.
      destruct c. 2:now constructor 2; apply IH.
      inv Hin. now repeat constructor. now constructor 2; apply IH.
    - match goal with |- Is_index_in_nclocks _ ?xs =>
        induction xs as [|nck anns IH] end. now inv Hin.
      destruct nck; simpl in *.
      now constructor 2; apply IH.
      destruct c. 2:now constructor 2; apply IH.
      inv Hin. now repeat constructor. now constructor 2; apply IH.
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

  Instance wc_patvar_Proper:
    Proper (@Permutation.Permutation (ident * clock)
               ==> @eq (list ident) ==> @eq (list nclock)
               ==> @eq ident ==> @eq sclock ==> iff) wc_patvar.
  Proof.
    intros env1 env2 Henv p1 p2 Hp nc1 nc2 Hncs x1 x2 Hx sck1 sck2 Hsck.
    subst. unfold wc_patvar.
    destruct (pinst (patsub nc2 p2) sck2);
      try rewrite Henv; reflexivity.
  Qed.

  (* Is there a double pointwise ? *)
  Lemma wc_patvar_Forall2_perm:
    forall env1 env2 pvars ncks xs cs,
      Permutation.Permutation env1 env2 ->
      (Forall2 (wc_patvar env1 pvars ncks) xs cs
       <-> Forall2 (wc_patvar env2 pvars ncks) xs cs).
  Proof.
    intros * Hperm.
    split; apply Forall2_impl_In; intros; rewrite Hperm in *; auto.
  Qed.

  Instance wc_equation_Proper:
    Proper (@eq global ==> @Permutation.Permutation (ident * clock)
                ==> @eq equation ==> iff)
           wc_equation.
  Proof.
    intros G1 G2 HG env1 env2 Henv eq1 eq2 Heq.
    rewrite Heq, HG. destruct eq2 as (xs & es).
    unfold wc_equation.
    rewrite (wc_patvar_Forall2_perm _ _ _ _ _ _ Henv).
    split; intro WCeq; destruct WCeq as (WCeq1 & WCeq2 & WCeq3); split; auto;
      apply Forall_impl_In with (2:=WCeq1); intros;
        rewrite Henv in *; auto.
  Qed.

End LCLOCKING.

Module LClockingFun
       (Ids  : IDS)
       (Op   : OPERATORS)
       (Syn  : LSYNTAX Ids Op)
       <: LCLOCKING Ids Op Syn.
  Include LCLOCKING Ids Op Syn.
End LClockingFun.
