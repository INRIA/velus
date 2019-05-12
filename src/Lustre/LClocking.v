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

  (* substitution of identifiers *)
  Definition ident_map := ident -> option ident.

  (* instantiate a parameter, giving a named clock *)
  Fixpoint inst (bck: clock) (sub: ident_map) (ick : clock) : option clock :=
    match ick with
    | Cbase => Some bck
    | Con ick' x b => match inst bck sub ick' with
                     | None => None
                     | Some ck' => option_map (fun y => Con ck' y b) (sub x)
                     end
    end.

  Definition WellInstantiated (bck : clock) (sub : ident_map)
                              (xc : ident * clock) (nc : nclock) : Prop :=
    sub (fst xc) = snd nc
    /\ inst bck sub (snd xc) = Some (fst nc).
            
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
        Forall2 eq (map ckstream anns) (clocksof e0s) ->
        Forall2 eq (map ckstream anns) (clocksof es) ->
        Forall unnamed_stream anns ->
        wc_exp (Efby e0s es anns)

    | wc_Ewhen: forall es x b tys ck,
        Forall wc_exp es ->
        In (x, ck) vars ->
        Forall (eq ck) (clocksof es) ->
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
        wc_exp (Eite e ets efs (tys, (ck, None)))

    | wc_Eapp: forall f es anns n,
        Forall wc_exp es ->
        find_node f G = Some n ->
        (exists bck sub,
            Forall2 (WellInstantiated bck sub) (idck n.(n_in)) (nclocksof es)
            /\ Forall2 (WellInstantiated bck sub) (idck n.(n_out)) (map snd anns)) ->
        wc_exp (Eapp f es anns).

    (* TODO: after experiment, maybe put in Common *)
    Definition LiftO {A} (d : Prop) (P : A -> Prop) (x : option A) : Prop :=
      match x with None => d | Some x => P x end.
    
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

    | IFEmerge: forall x ets efs anns,
        Exists (Is_fresh_in x) (ets ++ efs) ->
        Is_fresh_in x (Emerge x ets efs anns)

    | IFEifte: forall x e ets efs anns,
        Exists (Is_fresh_in x) (e :: (ets ++ efs)) ->
        Is_fresh_in x (Eite e ets efs anns)

    | IFEapp: forall x f es anns,
        Exists (Is_fresh_in x) es
        \/ Exists (fun y => LiftO True (eq x) (snd (snd y))) anns ->
        Is_fresh_in x (Eapp f es anns).

    (* TODO: Move to Common *)
    Fixpoint Ino {A} (a : A) (l : list (option A)) : Prop :=
      match l with
      | [] => False
      | b :: m => LiftO False (eq a) b \/ Ino a m
      end.

    (* TODO: Move to Common *)
    Inductive NoDupo {A} : list (option A) -> Prop :=
      NoDupo_nil : NoDupo []
    | NoDupo_cons : forall x l, ~ Ino x l -> NoDupo l -> NoDupo (Some x :: l).

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
      | Some x => InMembers x vars
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
        NoDupo (map snd (map snd anns)) ->
        Forall Is_AnonStream (map (snd ∘ snd) anns) ->
        DisjointFresh (Eapp f es anns).

    Definition WellFormedAnon (e : exp) : Prop :=
      match e with
      | Eapp f es anns =>
        Forall (fun x => ~Is_AnonStream x) (map (snd ∘ snd) anns)
        /\ DisjointFreshList es
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
        Forall2 eq (map ckstream anns) (clocksof e0s) ->
        Forall2 eq (map ckstream anns) (clocksof es) ->
        Forall unnamed_stream anns ->
        P (Efby e0s es anns).

    Hypothesis EwhenCase:
      forall es x b tys ck,
        Forall (wc_exp G vars) es ->
        Forall P es ->
        In (x, ck) vars ->
        Forall (eq ck) (clocksof es) ->
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
        P (Eite e ets efs (tys, (ck, None))).

    Hypothesis EappCase:
      forall f es anns n,
        Forall (wc_exp G vars) es ->
        Forall P es ->
        find_node f G = Some n ->
        (exists bck sub,
            Forall2 (WellInstantiated bck sub) (idck n.(n_in)) (nclocksof es)
            /\ Forall2 (WellInstantiated bck sub) (idck n.(n_out)) (map snd anns)) ->
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
        clear H2 H4. induction H; auto.
        clear H3 H5. induction H0; auto.
      - apply EiteCase; auto.
        clear H3 H5. induction H0; auto.
        clear H4 H6. induction H1; auto.
      - eapply EappCase; eauto.
        clear H0 H1. induction H; eauto.
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

  (*
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
   *)
  
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

  (*
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
   *)

End LCLOCKING.

Module LClockingFun
       (Ids  : IDS)
       (Op   : OPERATORS)
       (Syn  : LSYNTAX Ids Op)
       <: LCLOCKING Ids Op Syn.
  Include LCLOCKING Ids Op Syn.
End LClockingFun.
