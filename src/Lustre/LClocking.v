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

  (* substitution of identifiers *)
  Definition ident_map := ident -> option ident.

  (* xc : name and clock from the node interface
     nc : named clock from the annotated expression *)
  Definition WellInstantiated (bck : clock) (sub : ident_map)
                              (xc : ident * clock) (nc : nclock) : Prop :=
    sub (fst xc) = snd nc
    /\ instck bck sub (snd xc) = Some (fst nc).

  Section WellClocked.
    Context {PSyn : block -> Prop}.
    Context {prefs : PS.t}.

    Variable G    : @global PSyn prefs.
    Variable vars : list (ident * clock).

    Inductive wc_exp : exp -> Prop :=
    | wc_Econst: forall c,
        wc_exp (Econst c)

    | wc_Eenum: forall x ty,
        wc_exp (Eenum x ty)

    | wc_Evar: forall x ty ck,
        In (x, ck) vars ->
        wc_exp (Evar x (ty, ck))

    | wc_Eunop: forall op e ty ck,
        wc_exp e ->
        clockof e = [ck] ->
        wc_exp (Eunop op e (ty, ck))

    | wc_Ebinop: forall op e1 e2 ty ck,
        wc_exp e1 ->
        wc_exp e2 ->
        clockof e1 = [ck] ->
        clockof e2 = [ck] ->
        wc_exp (Ebinop op e1 e2 (ty, ck))

    | wc_Efby: forall e0s es anns,
        Forall wc_exp e0s ->
        Forall wc_exp es ->
        Forall2 eq (map snd anns) (clocksof e0s) ->
        Forall2 eq (map snd anns) (clocksof es) ->
        wc_exp (Efby e0s es anns)

    | wc_Earrow: forall e0s es anns,
        Forall wc_exp e0s ->
        Forall wc_exp es ->
        Forall2 eq (map snd anns) (clocksof e0s) ->
        Forall2 eq (map snd anns) (clocksof es) ->
        wc_exp (Earrow e0s es anns)

    | wc_Ewhen: forall es x ty b tys ck,
        In (x, ck) vars ->
        Forall wc_exp es ->
        Forall (eq ck) (clocksof es) ->
        length tys = length (clocksof es) ->
        wc_exp (Ewhen es x b (tys, (Con ck x (ty, b))))

    | wc_Emerge: forall x tx es tys ck,
        In (x, ck) vars ->
        es <> nil ->
        Forall (fun es => Forall wc_exp (snd es)) es ->
        Forall (fun '(i, es) => Forall (eq (Con ck x (tx, i))) (clocksof es)) es ->
        Forall (fun es => length tys = length (clocksof (snd es))) es ->
        wc_exp (Emerge (x, tx) es (tys, ck))

    | wc_Ecase: forall e es d tys ck,
        wc_exp e ->
        clockof e = [ck] ->
        es <> nil ->
        Forall (fun es => Forall wc_exp (snd es)) es ->
        Forall (fun es => Forall (eq ck) (clocksof (snd es))) es ->
        Forall (fun es => length tys = length (clocksof (snd es))) es ->
        (forall d0, d = Some d0 -> Forall wc_exp d0) ->
        (forall d0, d = Some d0 -> Forall (eq ck) (clocksof d0)) ->
        (forall d0, d = Some d0 -> length tys = length (clocksof d0)) ->
        wc_exp (Ecase e es d (tys, ck))

    | wc_Eapp: forall f es er anns n bck sub,
        Forall wc_exp es ->
        Forall wc_exp er ->
        find_node f G = Some n ->
        Forall2 (WellInstantiated bck sub) (idck (idty n.(n_in))) (nclocksof es) ->
        Forall2 (WellInstantiated bck sub) (idck (idty n.(n_out))) (map (fun '(_, ck) => (ck, None)) anns) ->
        Forall (fun e => exists ck, clockof e = [ck]) er ->
        wc_exp (Eapp f es er anns).

    Inductive wc_equation : equation -> Prop :=
    | wc_EqApp : forall xs f es er anns n bck sub,
        Forall wc_exp es ->
        Forall wc_exp er ->
        find_node f G = Some n ->
        Forall2 (WellInstantiated bck sub) (idck (idty n.(n_in))) (nclocksof es) ->
        Forall3 (fun xck ck2 x2 => WellInstantiated bck sub xck (ck2, Some x2)) (idck (idty n.(n_out))) (map snd anns) xs ->
        Forall (fun e => exists ck, clockof e = [ck]) er ->
        Forall2 (fun x ck => In (x, ck) vars) xs (map snd anns) ->
        wc_equation (xs, [Eapp f es er anns])
    | wc_Eq : forall xs es,
        Forall wc_exp es ->
        Forall2 (fun x ck => In (x, ck) vars) xs (clocksof es) ->
        wc_equation (xs, es).
  End WellClocked.

  Inductive wc_block {PSyn prefs} (G: @global PSyn prefs) : list (ident * clock) -> block -> Prop :=
  | wc_Beq : forall env eq,
      wc_equation G env eq ->
      wc_block G env (Beq eq)

  | wc_Breset : forall env blocks er ck,
      Forall (wc_block G env) blocks ->
      wc_exp G env er ->
      clockof er = [ck] ->
      wc_block G env (Breset blocks er)

  | wc_Bswitch : forall env env' ec branches ck,
      wc_exp G env ec ->
      clockof ec = [ck] ->
      branches <> nil ->
      (forall x ck', In (x, ck') env' -> In (x, ck) env /\ ck' = Cbase) ->
      Forall (fun blks => Forall (wc_block G env') (snd blks)) branches ->
      wc_block G env (Bswitch ec branches)

  | wc_Blocal : forall env locs blocks,
      Forall (wc_block G (env ++ idck (idty locs))) blocks ->
      Forall (wc_clock (env ++ idck (idty locs))) (map snd (idck (idty locs))) ->
      wc_block G env (Blocal locs blocks).

  Definition wc_node {PSyn prefs} (G: @global PSyn prefs) (n: @node PSyn prefs) : Prop
    :=    wc_env (idck (idty  n.(n_in)))
       /\ wc_env (idck (idty (n.(n_in) ++ n.(n_out))))
       /\ wc_block G (idck (idty (n.(n_in) ++ n.(n_out)))) n.(n_block).

  Definition wc_global {PSyn prefs} : @global PSyn prefs -> Prop :=
    wt_program wc_node.

  (** ** Basic properties of clocking *)

  Hint Constructors wc_exp wc_equation wc_block : lclocking.
  Hint Unfold wc_node wc_global wc_env : lclocking.

  Section wc_exp_ind2.
    Context (PSyn : block -> Prop).
    Context (prefs : PS.t).

    Variable G    : @global PSyn prefs.
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
        P (Evar x (ty, ck)).

    Hypothesis EunopCase:
      forall op e ty ck,
        wc_exp G vars e ->
        P e ->
        clockof e = [ck] ->
        P (Eunop op e (ty, ck)).

    Hypothesis EbinopCase:
      forall op e1 e2 ty ck,
        wc_exp G vars e1 ->
        P e1 ->
        wc_exp G vars e2 ->
        P e2 ->
        clockof e1 = [ck] ->
        clockof e2 = [ck] ->
        P (Ebinop op e1 e2 (ty, ck)).

    Hypothesis EfbyCase:
      forall e0s es anns,
        Forall (wc_exp G vars) e0s ->
        Forall (wc_exp G vars) es ->
        Forall P es ->
        Forall P e0s ->
        Forall2 eq (map snd anns) (clocksof e0s) ->
        Forall2 eq (map snd anns) (clocksof es) ->
        P (Efby e0s es anns).

    Hypothesis EarrowCase:
      forall e0s es anns,
        Forall (wc_exp G vars) e0s ->
        Forall (wc_exp G vars) es ->
        Forall P es ->
        Forall P e0s ->
        Forall2 eq (map snd anns) (clocksof e0s) ->
        Forall2 eq (map snd anns) (clocksof es) ->
        P (Earrow e0s es anns).

    Hypothesis EwhenCase:
      forall es x ty b tys ck,
        In (x, ck) vars ->
        Forall (wc_exp G vars) es ->
        Forall P es ->
        Forall (eq ck) (clocksof es) ->
        length tys = length (clocksof es) ->
        P (Ewhen es x b (tys, Con ck x (ty, b))).

    Hypothesis EmergeCase:
      forall x tx es tys ck,
        In (x, ck) vars ->
        es <> nil ->
        Forall (fun es => Forall (wc_exp G vars) (snd es)) es ->
        Forall (fun es => Forall P (snd es)) es ->
        Forall (fun '(i, es) => Forall (eq (Con ck x (tx, i))) (clocksof es)) es ->
        Forall (fun es => length tys = length (clocksof (snd es))) es ->
        P (Emerge (x, tx) es (tys, ck)).

    Hypothesis EcaseCase:
      forall e es d tys ck,
        wc_exp G vars e ->
        P e ->
        clockof e = [ck] ->
        es <> nil ->
        Forall (fun es => Forall (wc_exp G vars) (snd es)) es ->
        Forall (fun es => Forall P (snd es)) es ->
        Forall (fun es => Forall (eq ck) (clocksof (snd es))) es ->
        Forall (fun es => length tys = length (clocksof (snd es))) es ->
        (forall d0, d = Some d0 -> Forall (wc_exp G vars) d0) ->
        (forall d0, d = Some d0 -> Forall P d0) ->
        (forall d0, d = Some d0 -> Forall (eq ck) (clocksof d0)) ->
        (forall d0, d = Some d0 -> length tys = length (clocksof d0)) ->
        P (Ecase e es d (tys, ck)).

    Hypothesis EappCase:
      forall f es er anns n bck sub,
        Forall (wc_exp G vars) es ->
        Forall (wc_exp G vars) er ->
        Forall P es ->
        Forall P er ->
        find_node f G = Some n ->
        Forall2 (WellInstantiated bck sub) (idck (idty n.(n_in))) (nclocksof es) ->
        Forall2 (WellInstantiated bck sub) (idck (idty n.(n_out))) (map (fun '(_, ck) => (ck, None)) anns) ->
        Forall (fun e => exists ck, clockof e = [ck]) er ->
        P (Eapp f es er anns).

    Fixpoint wc_exp_ind2 (e: exp) (H: wc_exp G vars e) {struct H} : P e.
    Proof.
      destruct H; eauto.
      - apply EfbyCase; auto.
        + clear H2. induction H0; auto.
        + clear H1. induction H; auto.
      - apply EarrowCase; auto.
        + clear H2. induction H0; auto.
        + clear H1. induction H; auto.
      - apply EwhenCase; auto.
        clear H1 H2. induction H0; auto.
      - apply EmergeCase; auto.
        clear H0 H2 H3. induction H1; constructor; auto.
        induction H0; auto.
      - apply EcaseCase; auto.
        + clear H1 H3 H4. induction H2; constructor; auto.
          induction H1; auto.
        + intros; subst. clear H6 H7. specialize (H5 _ eq_refl).
          induction H5; auto.
      - eapply EappCase; eauto.
        + clear H1 H2. induction H; eauto.
        + clear H4. induction H0; eauto.
    Qed.

  End wc_exp_ind2.

  Lemma wc_global_NoDup {PSyn prefs}:
    forall (g: @global PSyn prefs),
      wc_global g ->
      NoDup (map n_name (nodes g)).
  Proof.
    intros * Wc.
    eapply wt_program_NoDup in Wc; eauto.
  Qed.

  Lemma wc_find_node {PSyn prefs}:
    forall (G: @global PSyn prefs) f n,
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

  Instance wc_exp_Proper {PSyn prefs}:
    Proper (@eq (@global PSyn prefs) ==> @Permutation.Permutation (ident * clock)
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

  (* Instance wc_exp_pointwise_Proper {PSyn prefs}: *)
  (*   Proper (@eq (@global PSyn prefs) ==> @Permutation.Permutation (ident * clock) *)
  (*               ==> pointwise_relation _ iff) *)
  (*          wc_exp. *)
  (* Proof. *)
  (*   intros G G' HG env' env Henv e. *)
  (*   now rewrite Henv, HG. *)
  (* Qed. *)

  Instance wc_equation_Proper {PSyn prefs}:
    Proper (@eq (@global PSyn prefs) ==> @Permutation.Permutation (ident * clock)
                ==> @eq equation ==> iff)
           wc_equation.
  Proof with auto.
    intros G1 G2 HG env1 env2 Henv eq1 eq2 Heq; subst.
    destruct eq2 as (xs & es). split; intros []; econstructor; eauto.
    1-10:rewrite Forall_forall in *; intros.
    1-10:(rewrite Henv in * || rewrite <-Henv in * || idtac); eauto.
    1-4:(setoid_rewrite Henv || setoid_rewrite <-Henv); auto.
  Qed.

  (* Instance wc_equation_pointwise_Proper {PSyn prefs}: *)
  (*   Proper (@eq (@global PSyn prefs) ==> @Permutation.Permutation (ident * clock) *)
  (*               ==> pointwise_relation _ iff) *)
  (*          wc_equation. *)
  (* Proof. *)
  (*   intros G1 G2 HG env1 env2 Henv eq; subst. now rewrite Henv. *)
  (* Qed. *)

  Instance wc_block_Proper {PSyn prefs}:
    Proper (@eq (@global PSyn prefs) ==> @Permutation.Permutation (ident * clock)
                ==> @eq block ==> iff)
           wc_block.
  Proof with auto.
    intros G1 G2 HG env1 env2 Henv d1 d2 Heq; subst. revert env1 env2 Henv.
    induction d2 using block_ind2; split; intros * Hwc; inv Hwc;
      econstructor; eauto.
    1,4,7:rewrite <-Henv; auto.
    1,4,6:rewrite Henv; auto.
    1-8:rewrite Forall_forall in *; eauto; intros.
    1-8:try rewrite <- H; eauto. 1-7:try rewrite <-Henv; auto. 1,2:rewrite Henv; auto.
  Qed.

  Instance wc_block_pointwise_Proper {PSyn prefs}:
    Proper (@eq (@global PSyn prefs) ==> @Permutation.Permutation (ident * clock)
                ==> pointwise_relation _ iff)
           wc_block.
  Proof with auto.
    intros G1 G2 HG env1 env2 Henv d; subst. now rewrite Henv.
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
    Context {PSyn : block -> Prop}.
    Context {prefs : PS.t}.
    Variable (G : @global PSyn prefs).

    Fact wc_clock_incl : forall vars vars' ck,
      incl vars vars' ->
      wc_clock vars ck ->
      wc_clock vars' ck.
    Proof.
      intros vars vars' ck Hincl Hwc.
      induction Hwc; auto.
    Qed.

    Lemma wc_exp_incl : forall vars vars' e,
        incl vars vars' ->
        wc_exp G vars e ->
        wc_exp G vars' e .
    Proof with eauto with lclocking.
      induction e using exp_ind2; intros Hincl Hwc; inv Hwc...
      1-6:econstructor; rewrite Forall_forall in *...
      1,2:intros ? Hin.
      - specialize (H _ Hin). specialize (H5 _ Hin). rewrite Forall_forall in *...
      - specialize (H _ Hin); simpl in H. specialize (H8 _ Hin).
        rewrite Forall_forall in *...
      - intros; subst; simpl in *. specialize (H11 _ eq_refl).
        rewrite Forall_forall in *...
    Qed.

    Lemma wc_equation_incl : forall vars vars' eq,
        incl vars vars' ->
        wc_equation G vars eq ->
        wc_equation G vars' eq.
    Proof with eauto.
      intros vars vars' [xs es] Hincl Hwc.
      inv Hwc; econstructor; eauto.
      1,2,4:rewrite Forall_forall in *; eauto using wc_exp_incl.
      1,2:eapply Forall2_impl_In; eauto; intros; simpl in *; auto.
    Qed.

    Lemma wc_block_incl : forall d vars vars',
        incl vars vars' ->
        wc_block G vars d ->
        wc_block G vars' d .
    Proof.
      induction d using block_ind2; intros * Incl Wt; inv Wt.
      - constructor. eauto using wc_equation_incl.
      - econstructor; eauto using wc_exp_incl.
        rewrite Forall_forall in *; intros; eauto.
      - econstructor. 1-6:eauto using wc_exp_incl.
        intros. edestruct H6; eauto.
      - constructor.
        1,2:rewrite Forall_forall in *; intros; eauto using incl_appl'.
        eapply wc_clock_incl; eauto using incl_appl'.
    Qed.

  End incl.

  (** ** Validation *)

  Hint Extern 2 (In _ (idck _)) => apply In_idck_exists.

  Section ValidateExpression.
    Context {PSyn : block -> Prop}.
    Context {prefs : PS.t}.

    Variable G : @global PSyn prefs.
    Variable venv : Env.t clock.

    Open Scope option_monad_scope.

    Definition check_var (x : ident) (ck : clock) : bool :=
      match Env.find x venv with
      | None => false
      | Some xc => ck ==b xc
      end.

    Definition check_paired_clocks (nc1 nc2 : clock) (tc : ann) : bool :=
      match tc with
      | (t, c) => (nc1 ==b c) && (nc2 ==b c)
      end.

    Definition check_merge_clocks {A} (x : ident) (tx : type) (ck : clock) (ncs : list (enumtag * list clock)) (n : nat) (tys : list A) : bool :=
      forallb (fun '(i, ncs) => forallb (fun ck' => ck' ==b (Con ck x (tx, i))) ncs
                             && (length ncs ==b length tys)) ncs.

    Definition check_case_clocks {A} (ck : clock) (ncs : list (list clock)) (tys : list A) : bool :=
      forallb (fun ncs => forallb (fun ck' => ck' ==b ck) ncs
                       && (length ncs ==b length tys)) ncs.

    Definition add_isub
               (sub : Env.t ident)
               (nin : (ident * (type * clock * ident)))
               (nc : nclock) : Env.t ident :=
      match snd nc, nin with
      | Some y, (x, (xt, xc, xcaus)) => Env.add x y sub
      | None, _ => sub
      end.

    Definition add_osub
               (sub : Env.t ident)
               (nin : (ident * (type * clock * ident)))
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

    Definition check_reset (ckr : list (list clock)) : bool :=
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

    Fixpoint check_exp (e : exp) : option (list clock) :=
      match e with
      | Econst c => Some [Cbase]

      | Eenum _ _ => Some [Cbase]

      | Evar x (xt, xc) =>
        if (check_var x xc) then Some [xc] else None

      | Eunop op e (xt, xc) =>
        do nce <- assert_singleton (check_exp e);
        if xc ==b nce then Some [xc] else None

      | Ebinop op e1 e2 (xt, xc) =>
        do nc1 <- assert_singleton (check_exp e1);
        do nc2 <- assert_singleton (check_exp e2);
        if (xc ==b nc1) && (xc ==b nc2) then Some [xc] else None

      | Efby e0s es anns =>
        do nc0s <- oconcat (map check_exp e0s);
        do ncs <- oconcat (map check_exp es);
        if forall3b check_paired_clocks nc0s ncs anns
        then Some (map snd anns) else None

      | Earrow e0s es anns =>
        do nc0s <- oconcat (map check_exp e0s);
        do ncs <- oconcat (map check_exp es);
        if forall3b check_paired_clocks nc0s ncs anns
        then Some (map snd anns) else None

      | Ewhen es x b (tys, nc) =>
        match nc with
        | Con xc y (_, yb) =>
          do nces <- oconcat (map check_exp es);
          if (x ==b y) && (b ==b yb) && (check_var x xc)
             && (forall2b (fun c _ => xc ==b c) nces tys)
          then Some (map (fun _ => nc) tys) else None
        | _ => None
        end

      | Emerge (x, tx) es (tys, ck) =>
        do ncs <- omap (fun es => oconcat (map check_exp (snd es))) es;
        if check_var x ck && check_merge_clocks x tx ck (combine (map fst es) ncs) (length es) tys
           && (negb (is_nil es))
        then Some (map (fun _ => ck) tys) else None

      | Ecase e brs d (tys, ck) =>
        do nds <- or_default_with (Some []) (fun d => do nds <- oconcat (map check_exp d); Some [nds]) d;
        do ncs <- omap (fun es => oconcat (map check_exp (snd es))) brs;
        do ce <- assert_singleton (check_exp e);
        if (ce ==b ck) && check_case_clocks ck (nds++ncs) tys
           && (negb (is_nil brs))
        then Some (map (fun _ => ck) tys) else None

      | Eapp f es er anns =>
        do n <- find_node f G;
        do _ <- oconcat (map check_exp es);
        do nr <- omap check_exp er;
        do nin0 <- option_map (fun '(_, (_, ck, _)) => ck) (hd_error n.(n_in));
        let nces := nclocksof es in
        do nces0 <- option_map fst (hd_error nces);
        do bck <- find_base_clock nin0 nces0;
        let nanns := map (fun '(ty, ck) => (ty, (ck, None))) anns in
        let isub := fold_left2 add_isub n.(n_in) nces (Env.empty ident) in
        let sub := fold_left2 add_osub n.(n_out) nanns isub in
        if (forall2b (fun '(_, (_, ck, _)) '(ck', _) => check_inst bck sub ck ck')
                     n.(n_in) nces)
           && (forall2b (fun '(_, (_, ck, _)) '(_, (ck', _)) => check_inst bck sub ck ck')
                        n.(n_out) nanns)
           && (check_reset nr)
        then Some (map snd anns) else None

      end.

    Definition check_rhs (xs : list ident) (e : exp) : option (list clock) :=
      match e with
      | Eapp f es er anns =>
        do n <- find_node f G;
        do _ <- oconcat (map check_exp es);
        do nr <- omap check_exp er;
        do nin0 <- option_map (fun '(_, (_, ck, _)) => ck) (hd_error n.(n_in));
        let nces := nclocksof es in
        do nces0 <- option_map fst (hd_error nces);
        do bck <- find_base_clock nin0 nces0;
        let nanns := map (fun '((ty, ck), x) => (ty, (ck, Some x))) (combine anns xs) in
        let isub := fold_left2 add_isub n.(n_in) nces (Env.empty ident) in
        let sub := fold_left2 add_osub n.(n_out) nanns isub in
        if (forall2b (fun '(_, (_, ck, _)) '(ck', _) => check_inst bck sub ck ck')
                     n.(n_in) nces)
           && (length xs ==b length anns)
           && (forall2b (fun '(_, (_, ck, _)) '(_, ck') => check_inst bck sub ck ck')
                        n.(n_out) anns)
           && (check_reset nr)
        then Some (map snd anns) else None

      | _ => check_exp e
      end.

    Definition check_equation (eq : equation) : bool :=
      let '(xs, es) := eq in
      match es with
      | [Eapp f es er anns] =>
        match
          (do n <- find_node f G;
           do _ <- oconcat (map check_exp es);
           do nr <- omap check_exp er;
           do nin0 <- option_map (fun '(_, (_, ck, _)) => ck) (hd_error n.(n_in));
           let nces := nclocksof es in
           do nces0 <- option_map fst (hd_error nces);
           do bck <- find_base_clock nin0 nces0;
           let nanns := map (fun '((ty, ck), x) => (ty, (ck, Some x))) (combine anns xs) in
           let isub := fold_left2 add_isub n.(n_in) nces (Env.empty ident) in
           let sub := fold_left2 add_osub n.(n_out) nanns isub in
           if (forall2b (fun '(_, (_, ck, _)) '(ck', _) => check_inst bck sub ck ck')
                        n.(n_in) nces)
              && (length xs ==b length anns)
              && (forall2b (fun '(_, (_, ck, _)) '(_, ck') => check_inst bck sub ck ck')
                           n.(n_out) anns)
              && (check_reset nr)
           then Some (map snd anns) else None)
        with
        | None => false
        | Some ncks => forall2b check_var xs ncks
        end
      | _ => match oconcat (map check_exp es) with
            | None => false
            | Some ncks => forall2b check_var xs ncks
            end
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

    Corollary check_vars_correct: forall xs cks,
        forall2b check_var xs cks = true ->
        Forall2 (fun x ck => In (x, ck) (Env.elements venv)) xs cks.
    Proof.
      intros * Hf2.
      apply forall2b_Forall2 in Hf2.
      eapply Forall2_impl_In; [|eauto]; intros.
      eapply check_var_correct; eauto.
    Qed.

    Lemma check_paired_clocks_correct:
      forall cks1 cks2 anns,
        forall3b check_paired_clocks cks1 cks2 anns = true ->
        cks1 = map snd anns
        /\ cks2 = map snd anns.
    Proof.
      setoid_rewrite forall3b_Forall3.
      induction 1 as [|ck1 ck2 (ty, ck) cks1 cks2 anns
                                 IH1 IH2 (Hcks1 & Hcks2)];
        subst; simpl in *; eauto.
      rewrite Bool.andb_true_iff in IH1.
      setoid_rewrite equiv_decb_equiv in IH1.
      destruct IH1 as (Hck1 & Hck2). inv Hck1; inv Hck2.
      f_equal; auto.
    Qed.

    Lemma check_merge_clocks_correct:
      forall {A} x tx ck ncs n (tys : list A),
        check_merge_clocks x tx ck ncs n tys = true ->
        Forall (fun '(i, ncs) => Forall (fun ck' => (Con ck x (tx, i)) = ck') ncs) ncs /\
        Forall (fun '(_, ncs) => length ncs = length tys) ncs.
    Proof.
      intros * CM; unfold check_merge_clocks in CM.
      rewrite forallb_Forall in CM.
      split; (eapply Forall_impl; [|eauto]); intros (?&?) CM';
        rewrite Bool.andb_true_iff, forallb_Forall in CM'; destruct CM' as (CM1&CM2).
      - eapply Forall_impl; [|eauto]. intros ? Heq; simpl in *.
        rewrite equiv_decb_equiv in Heq. inv Heq; auto.
      - rewrite equiv_decb_equiv in CM2; inv CM2; auto.
    Qed.

    Lemma check_case_clocks_correct:
      forall {A} ck ncs (tys : list A),
        check_case_clocks ck ncs tys = true ->
        Forall (Forall (fun ck' => ck = ck')) ncs /\
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
            wc_exp G (Env.elements venv) e /\ clockof e = cks) ->
        oconcat (map f es) = Some cks ->
        Forall (wc_exp G (Env.elements venv)) es
        /\ clocksof es = cks.
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
      forall {f} (ess : list (enumtag * _)) ncks,
        (forall es e ncks,
            In es ess ->
            In e (snd es) ->
            f e = Some ncks ->
            wc_exp G (Env.elements venv) e /\ clockof e = ncks) ->
        omap (fun es => oconcat (map f (snd es))) ess = Some ncks ->
        Forall (fun es => Forall (wc_exp G (Env.elements venv)) (snd es)) ess
        /\ Forall2 (fun es ncks => clocksof (snd es) = ncks) ess ncks.
    Proof.
      induction ess as [|es ess IH]; intros ncks WTf CE. now inv CE; auto.
      simpl in CE. destruct (oconcat (map f (snd es))) eqn:Ce; [|now omonadInv CE].
      eapply oconcat_map_check_exp' in Ce as (?&?); eauto with datatypes.
      destruct (omap _ _) as [tes|]; [|now omonadInv CE].
      omonadInv CE. simpl.
      specialize (IH tes) as (? & ?); eauto using in_cons.
    Qed.

    Lemma omap_check_exp':
      forall {f} es cks,
        (forall e cks,
            In e es ->
            f e = Some cks ->
            wc_exp G (Env.elements venv) e /\ clockof e = cks) ->
        omap f es = Some cks ->
        Forall (wc_exp G (Env.elements venv)) es
        /\ Forall2 (fun e ck => clockof e = ck) es cks.
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
      unfold add_isub; simpl. intros sub x ((ty, ck), ?) ? nm NI.
      destruct nm. now rewrite Env.gss.
      now apply Env.Props.P.F.not_find_in_iff in NI.
    Qed.

    Lemma fold_left2_add_osub_skip:
      forall x xs anns sub,
        ~In x (map fst xs) ->
        Env.find x (fold_left2 add_osub xs anns sub) = Env.find x sub.
    Proof.
      induction xs as [|(y, ((yt, yc), ycaus)) xs IH]; simpl; auto.
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
      induction xs as [|(y, ((yt, yc), ycaus)) xs IH]; simpl; auto.
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
      induction xs as [|(y, ((yt, yc), ycaus)) xs IH]. now inversion 1.
      intros ncs sub Ix ND NI.
      destruct ncs as [|(ck', nm') ncs]. now inversion Ix.
      simpl in *.
      destruct Ix as [Ix|Ix].
      - inv Ix. inv ND. rewrite fold_left2_add_isub_skip.
        now apply find_add_isub.
        rewrite in_map_iff.
        intros ((y, ((?, ?), ?)) & Fy & Iy). simpl in *; subst.
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
      induction xs as [|(y, ((yt, yc), ycaus)) xs IH]. now inversion 1.
      intros ncs sub Ix ND NI.
      destruct ncs as [|(ck', nm') ncs]. now inversion Ix.
      simpl in *.
      destruct Ix as [Ix|Ix].
      - inv Ix. inv ND. rewrite fold_left2_add_osub_skip.
        now apply find_add_isub.
        rewrite in_map_iff.
        intros ((y, ((?, ?), ?)) & Fy & Iy). simpl in *; subst.
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
      destruct a as [|? [|??]]; try congruence; eauto.
    Qed.

    Local Hint Constructors wc_exp.
    Lemma check_exp_correct:
      forall e ncks,
        check_exp e = Some ncks ->
        wc_exp G (Env.elements venv) e
        /\ clockof e = ncks.
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
                 apply check_paired_clocks_correct in H as (? & ?)
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
      - (* Eunop *)
        apply IHe in OE0 as (? & ?).
        eauto.
      - (* Ebinop *)
        apply IHe1 in OE0 as (? & ?); apply IHe2 in OE1 as (? & ?).
        eauto.
      - (* Efby *)
        repeat take (Forall (fun e :exp => _) _) and rewrite Forall_forall in it.
        apply oconcat_map_check_exp' in OE0 as (? & ?); auto.
        apply oconcat_map_check_exp' in OE1 as (? & ?); auto. subst.
        split; eauto.
      - (* Earrow *)
        repeat take (Forall (fun e :exp => _) _) and rewrite Forall_forall in it.
        apply oconcat_map_check_exp' in OE0 as (? & ?); auto.
        apply oconcat_map_check_exp' in OE1 as (? & ?); auto. subst.
        split; eauto.
      - (* Ewhen *)
        take (Forall _ es) and rewrite Forall_forall in it.
        take (oconcat (map check_exp _) = Some _) and
             apply oconcat_map_check_exp' in it as (? & ?); auto.
        take (forall2b _ _ _ = true) and rename it into FA2; apply forall2b_Forall2 in FA2.
        subst; simpl; repeat split; auto. constructor; auto.
        2:pose proof (Forall2_length _ _ _ FA2) as Hlen; auto.
        apply Forall2_ignore2 in FA2.
        apply Forall_impl_In with (2:=FA2). intros ? ? (? & HH).
        now rewrite equiv_decb_equiv in HH; inv HH.
      - (* Emerge *)
        take (Forall _ es) and (repeat setoid_rewrite Forall_forall in it).
        take (omap _ _ = Some _) and
             apply omap_concat_map_check_exp' in it as (Hwc & Heq); eauto.
        take (check_merge_clocks _ _ _ _ _ _ = true) and
             apply check_merge_clocks_correct in it as (Hf1 & Hf2).
        eapply Forall2_combine'' in Hf1. eapply Forall2_combine'' in Hf2.
        2,3:(rewrite map_length; eapply Forall2_length in Heq; eauto).
        split; eauto. econstructor; eauto.
        + contradict H1; subst; simpl. auto.
        + rewrite Forall2_map_1 in Hf1. eapply Forall2_Forall2 in Hf1; [|eapply Heq].
          eapply Forall2_ignore2 in Hf1. eapply Forall_impl; [|eauto]. intros (?&?) (?&_&Hck&?); simpl in *; subst.
          assumption.
        + rewrite Forall2_map_1 in Hf2. eapply Forall2_Forall2 in Hf2; [|eapply Heq].
          eapply Forall2_ignore2 in Hf2. eapply Forall_impl; [|eauto]. intros (?&?) (?&_&Hlen&?); simpl in *.
          rewrite Hlen; auto.
      - (* Ecase *)
        take (Forall _ _) and (repeat setoid_rewrite Forall_forall in it).
        take (omap _ _ = Some _) and
             apply omap_concat_map_check_exp' in it as (Hwces & Hckes); eauto.
        (* take (oconcat (map check_exp _) = Some _) and *)
        (*      apply oconcat_map_check_exp' in it as (? & ?); eauto. *)
        take (check_case_clocks _ _ _ = true) and
             apply check_case_clocks_correct in it as (Hf1 & Hf2).
        apply Forall_app in Hf1 as (Hd1&Hes1). apply Forall_app in Hf2 as (Hd2&Hes2).
        (* eapply forallb_Forall in H3. *)
        eapply IHe in OE2 as (? & Hcke); auto.
        split; eauto. econstructor; eauto.
        + contradict H2; subst; simpl. auto.
        + eapply Forall2_ignore2 in Hckes.
          eapply Forall_impl; [|eapply Hckes]; intros (?&?) (?&?&Hck); subst.
          eapply Forall_forall in Hes1; eauto.
        + eapply Forall2_ignore2 in Hckes.
          eapply Forall_impl; [|eapply Hckes]; intros (?&?) (?&?&Hck).
          rewrite Hck.
          eapply Forall_forall in Hes2; eauto.
        + intros; subst; simpl in *. destruct (oconcat (map _ _)) eqn:OE1; simpl in *; omonadInv OE0.
          take (oconcat (map check_exp _) = Some _) and
             apply oconcat_map_check_exp' in it as (? & ?); eauto.
          intros; eapply Forall_forall in H0; eauto.
        + intros; subst; simpl in *. destruct (oconcat (map _ _)) eqn:OE1; simpl in *; omonadInv OE0.
          take (oconcat (map check_exp _) = Some _) and
             apply oconcat_map_check_exp' in it as (? & ?); eauto.
          2:intros; eapply Forall_forall in H0; eauto. rewrite H3.
          apply Forall_singl in Hd1; auto.
        + intros; subst; simpl in *. destruct (oconcat (map _ _)) eqn:OE1; simpl in *; omonadInv OE0.
          take (oconcat (map check_exp _) = Some _) and
             apply oconcat_map_check_exp' in it as (? & ?); eauto.
          2:intros; eapply Forall_forall in H0; eauto.
          rewrite H3.
          now apply Forall_singl in Hd2.
      - (* Eapp *)
        repeat take (Forall _ _) and rewrite Forall_forall in it.
        take (oconcat (map check_exp _) = Some _) and
             apply oconcat_map_check_exp' in it as (? & ?); auto. subst.
        repeat take (forall2b _ _ _ = true) and apply forall2b_Forall2 in it.
        split; auto.
        match goal with H:find_base_clock _ _ = Some ?c |- _ => rename c into bck end.

        assert (Forall2 (WellInstantiated bck
           (fun x => Env.find x (fold_left2 add_osub n.(n_out) (map (fun '(ty, ck0) => (ty, (ck0, None))) a)
              (fold_left2 add_isub n.(n_in) (nclocksof es) (Env.empty _)))))
                        (idck (idty n.(n_in))) (nclocksof es)).
        { apply Forall2_map_1, Forall2_map_1, Forall2_forall.
          take (Forall2 _ n.(n_in) (nclocksof es)) and rename it into FA2.
          split; [|now apply Forall2_length with (1:=FA2)].
          intros (x, ((xt, xc), xcaus)) (ck, nm) Ix.
          constructor; simpl;
            [|now apply Forall2_In with (1:=Ix), check_inst_correct in FA2].
          pose proof n.(n_nodup) as (ND&_).
          rewrite fold_left2_add_osub_skip, fold_left2_add_isub with (1:=Ix); eauto using NoDupMembers_app_l.
          now rewrite Env.Props.P.F.empty_in_iff.
          apply in_combine_l, In_InMembers in Ix.
          rewrite <-fst_InMembers.
          apply NoDupMembers_app_InMembers with (2:=Ix).
          solve_NoDupMembers_app. }

        assert (Forall2 (WellInstantiated bck
           (fun x => Env.find x (fold_left2 add_osub n.(n_out) (map (fun '(ty, ck0) => (ty, (ck0, None))) a)
             (fold_left2 add_isub n.(n_in) (nclocksof es) (Env.empty ident)))))
                        (idck (idty n.(n_out))) (map (fun '(ty, ck0) => (ck0, None)) a)).
        { apply Forall2_map_1, Forall2_map_1, Forall2_forall.
          take (Forall2 _ n.(n_out) _) and rename it into FA2.
          split. 2:{ eapply Forall2_length in FA2. rewrite map_length in *; auto. }
          intros (x, ((xt, xc), xcaus)) (ck, nm) Ix.
          rewrite combine_map_snd, in_map_iff in Ix.
          destruct Ix as (((y & ((yt & yc) & ycaus)), (yc' & ynm)) & EE & Ix); inv EE.
          constructor; simpl.
          2:{ rewrite Forall2_map_2 in FA2. eapply Forall2_In in Ix; [|eauto]; simpl in *.
              apply check_inst_correct; auto. }
          pose proof n.(n_nodup) as (ND&_).
          erewrite fold_left2_add_osub ; eauto. 2:solve_NoDupMembers_app.
          { rewrite combine_map_snd. eapply in_map_iff; do 2 esplit; eauto; simpl; auto. }
          setoid_rewrite Env.Props.P.F.not_find_in_iff.
          rewrite fold_left2_add_isub_skip; auto using Env.gempty.
          rewrite <-fst_InMembers.
          apply in_combine_l, In_InMembers in Ix.
          apply NoDupMembers_app_InMembers with (2:=Ix).
          rewrite Permutation_app_comm. solve_NoDupMembers_app. }

        eapply omap_check_exp' in OE2 as (? & ?); eauto.
        econstructor; eauto.
        + eapply check_reset_correct in H2.
          eapply Forall2_ignore1' in H2. 2:symmetry; eapply Forall2_length; eauto.
          eapply Forall2_Forall2, Forall2_ignore2 in H4; eauto.
          eapply Forall_impl; [|eauto]. intros ? (?&?&?&?); subst.
          auto.
    Qed.

    Corollary omap_check_exp:
      forall es ncks,
        omap check_exp es = Some ncks ->
        Forall (wc_exp G (Env.elements venv)) es
        /\ Forall2 (fun e ck => clockof e = ck) es ncks.
    Proof.
      intros.
      eapply omap_check_exp'; eauto.
      intros; eauto using check_exp_correct.
    Qed.

    Corollary oconcat_map_check_exp:
      forall es ncks,
        oconcat (map check_exp es) = Some ncks ->
        Forall (wc_exp G (Env.elements venv)) es
        /\ clocksof es = ncks.
    Proof.
      intros.
      eapply oconcat_map_check_exp'; eauto.
      intros; eauto using check_exp_correct.
    Qed.

    Lemma check_equation_correct:
      forall eq,
        check_equation eq = true ->
        wc_equation G (Env.elements venv) eq.
    Proof.
      intros eq CE. destruct eq as (xs, es); simpl in CE.
      cases_eqn CE.
      1-13:take (forall2b _ _ _ = true) and apply check_vars_correct in it.
      1-11,13:(take (oconcat (map _ _) = Some _)
                    and apply oconcat_map_check_exp in it as (WC & NC);
               econstructor; eauto; rewrite NC; auto).
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
             | H:forall3b check_paired_clocks ?cks1 ?cks2 ?anns = true |- _ =>
               apply check_paired_clocks_correct in H as (? & ?)
             | H:(?xs <>b 0) = true |- _ =>
               apply nequiv_decb_true in H;
                 assert (0 < xs) by (destruct l;
                                     [now exfalso; apply H|apply PeanoNat.Nat.lt_0_succ])
             | H:obind2 (assert_singleton ?ce) _ = Some _ |- _ =>
               destruct (assert_singleton ce) as [(ck, n)|] eqn:AS;
                 try discriminate; simpl in H
             end.

      (* app *)
      repeat take (Forall _ _) and rewrite Forall_forall in it.
      take (oconcat (map check_exp _) = Some _) and
           apply oconcat_map_check_exp in it as (? & ?); auto. subst.
      take (omap check_exp _ = Some _) and
           apply omap_check_exp in it as (?&?); auto. subst.
      repeat take (forall2b _ _ _ = true) and apply forall2b_Forall2 in it.
      match goal with H:find_base_clock _ _ = Some ?c |- _ => rename c into bck end.

      assert (Forall2 (WellInstantiated bck
                                        (fun x => Env.find x (fold_left2 add_osub n.(n_out) (map (fun '(ty, ck0, x0) => (ty, (ck0, Some x0))) (combine l2 xs))
                                                                                         (fold_left2 add_isub n.(n_in) (nclocksof l0) (Env.empty _)))))
                      (idck (idty n.(n_in))) (nclocksof l0)).
      { apply Forall2_map_1, Forall2_map_1, Forall2_forall.
        take (Forall2 _ n.(n_in) (nclocksof l0)) and rename it into FA2.
        split; [|now apply Forall2_length with (1:=FA2)].
        intros (x, ((xt, xc), xcaus)) (ck, nm) Ix.
        constructor; simpl;
          [|now apply Forall2_In with (1:=Ix), check_inst_correct in FA2].
        pose proof n.(n_nodup) as (ND&_).
        rewrite fold_left2_add_osub_skip, fold_left2_add_isub with (1:=Ix); eauto using NoDupMembers_app_l.
        now rewrite Env.Props.P.F.empty_in_iff.
        apply in_combine_l, In_InMembers in Ix.
        rewrite <-fst_InMembers.
        apply NoDupMembers_app_InMembers with (2:=Ix).
        solve_NoDupMembers_app. }

      assert (Forall3 (fun xck ck2 x2 =>
                         WellInstantiated bck
                                          (fun x => Env.find x (fold_left2 add_osub n.(n_out) (map (fun '(ty, ck0, x0) => (ty, (ck0, Some x0))) (combine l2 xs))
                                                                                           (fold_left2 add_isub n.(n_in) (nclocksof l0) (Env.empty ident))))
                                          xck (ck2, Some x2))
                      (idck (idty n.(n_out))) (map snd l2) xs).
      { apply Forall3_combine2, Forall2_map_1, Forall2_map_1, Forall2_forall; simpl.
        rewrite map_length; auto.
        take (Forall2 _ n.(n_out) _) and rename it into FA2.
        split. 2:{ eapply Forall2_length in FA2.
                   rewrite combine_length, map_length, H4, Nat.min_id; auto. }
        intros (x, ((xt, xc), xcaus)) (ck, nm) Ix.
        rewrite combine_map_fst, combine_map_snd, in_map_iff in Ix.
        destruct Ix as (((y & ((yt & yc) & ycaus)), ((? & yc') & ynm)) & EE & Ix); inv EE.
        constructor; simpl.
        2:{ eapply Forall2_In in FA2; [|eauto]; simpl in *.
            2:{ eapply In_combine_nth_error in Ix as (?&?&Hnth2). apply combine_nth_error in Hnth2 as (Hnth2&Hnth3).
                eapply In_combine_nth_error; eauto. }
            simpl in *. eapply check_inst_correct; eauto. }
        pose proof n.(n_nodup) as (ND&_).
        erewrite fold_left2_add_osub ; eauto. 2:solve_NoDupMembers_app.
        { rewrite combine_map_snd. eapply in_map_iff; do 2 esplit; eauto; simpl; auto. }
        setoid_rewrite Env.Props.P.F.not_find_in_iff.
        rewrite fold_left2_add_isub_skip; auto using Env.gempty.
        rewrite <-fst_InMembers.
        apply in_combine_l, In_InMembers in Ix.
        apply NoDupMembers_app_InMembers with (2:=Ix).
        rewrite Permutation_app_comm. solve_NoDupMembers_app. }

      econstructor; eauto.
      + eapply check_reset_correct in H0.
        eapply Forall2_ignore1' in H0. 2:symmetry; eapply Forall2_length; eauto.
        eapply Forall2_Forall2, Forall2_ignore2 in H5; eauto.
        eapply Forall_impl; [|eauto]. intros ? (?&?&?&?); subst.
        auto.
    Qed.

  End ValidateExpression.

  Fixpoint check_clock xenv (ck : clock) : bool :=
    match ck with
    | Cbase => true
    | Con ck' x b =>
      check_var xenv x ck' && check_clock xenv ck'
    end.

  Lemma check_clock_correct : forall xenv ck,
      check_clock xenv ck = true ->
      wc_clock (Env.elements xenv) ck.
  Proof.
    induction ck; intros Hcheck; simpl; auto.
    apply Bool.andb_true_iff in Hcheck as [Hc1 Hc2].
    constructor; auto.
    rewrite check_var_correct in Hc1; auto.
  Qed.

  Section ValidateBlock.
    Context {PSyn : block -> Prop}.
    Context {prefs : PS.t}.
    Variable (G : @global PSyn prefs).

    Fixpoint check_block (venv : Env.t clock) (blk : block) : bool :=
      match blk with
      | Beq eq => check_equation G venv eq
      | Breset blocks er =>
        forallb (check_block venv) blocks &&
        match check_exp G venv er with
        | Some [ck] => true
        | _ => false
        end
      | Bswitch ec branches =>
        negb (is_nil branches) &&
        match check_exp G venv ec with
        | Some [ck] =>
          let venv' := Env.Props.P.filter (fun x ck' => (ck' ==b ck)) venv in
          let venv' := Env.map (fun _ => Cbase) venv' in
          forallb (fun blks => forallb (check_block venv') (snd blks)) branches
        | _ => false
        end
      | Blocal locs blocks =>
        let venv' := Env.union venv (Env.from_list (idck (idty locs))) in
        forallb (check_block venv') blocks &&
        forallb (check_clock venv') (map snd (idck (idty locs)))
      end.

    Ltac solve_ndup :=
      unfold idck in *; simpl in *; solve_NoDupMembers_app.

    Lemma check_block_correct: forall blk venv,
        NoDupLocals (map fst (Env.elements venv)) blk ->
        check_block venv blk = true ->
        wc_block G (Env.elements venv) blk.
    Proof.
      induction blk using block_ind2; intros * ND CE; simpl in *; inv ND.
      - (* equation *)
        econstructor. eapply check_equation_correct; eauto.
      - (* reset *)
        apply Bool.andb_true_iff in CE as (CDs&CE).
        cases_eqn CEr; subst.
        eapply check_exp_correct in CEr as (?&Hnck).
        econstructor; auto.
        + eapply forallb_Forall in CDs.
          rewrite Forall_forall in *; intros; eauto.
        + eauto.
      - (* switch *)
        apply Bool.andb_true_iff in CE as (CNnil&CE).
        cases_eqn CE; subst.
        eapply check_exp_correct in CE0 as (?&Hck).
        remember (Env.Props.P.filter _ _) as venv'.
        assert (incl (Env.elements venv') (Env.elements venv)) as Hincl.
        { subst. intros (?&?) Hin.
          apply Env.elements_correct.
          apply Env.elements_complete, Env.Props.P.filter_iff in Hin as (?&?); auto.
          intros ??????; subst; auto. }
        econstructor. 1-6:eauto.
        3:{ eapply forallb_Forall in CE. do 2 (eapply Forall_forall; intros).
            repeat (take (Forall _ branches) and eapply Forall_forall in it; eauto).
            eapply forallb_Forall in it1.
            repeat (take (Forall _ _) and eapply Forall_forall in it; eauto).
            eapply it2. 2:eauto.
            eapply NoDupLocals_incl; eauto using incl_map.
            etransitivity; [|eapply incl_map; eauto].
            eapply Env.refines_elements with (R:= fun _ _ => True). intros ?? Hfind.
            rewrite Env.Props.P.F.map_o in Hfind. eapply option_map_inv in Hfind as (?&Hfind&?); eauto.
        }
        + contradict CNnil; subst; simpl in *. auto.
        + subst. intros ?? Hin.
          eapply Env.elements_complete in Hin. rewrite Env.Props.P.F.map_o in Hin.
          apply option_map_inv in Hin as (?&?&?); subst. split; auto.
          apply Env.Props.P.filter_iff in H1 as (?&Heq); auto.
          2:{ intros ??????; subst; auto. }
          apply clock_eqb_eq in Heq; subst.
          apply Env.elements_correct; auto.
      - (* local *)
        apply Bool.andb_true_iff in CE as (CB&CC).
        apply forallb_Forall in CB. apply forallb_Forall in CC.
        constructor.
        1,2:rewrite Forall_forall in *; intros.
        + eapply H in CB; eauto.
          eapply wc_block_incl; eauto.
          1,2:rewrite Env.elements_union. 1,3:rewrite Env.elements_from_list. reflexivity.
          1,3:eapply NoDupMembers_idck, NoDupMembers_idty; eauto.
          rewrite map_app, map_fst_idck, map_fst_idty; eauto.
          1,2:intros ? Hin Hinlocs; eapply H5.
          1,3:eapply Env.In_from_list in Hinlocs; rewrite InMembers_idck, InMembers_idty in Hinlocs; eauto.
          1,2:eapply fst_InMembers, Env.In_Members; eauto.
        + eapply check_clock_correct in CC; eauto.
          eapply wc_clock_incl; eauto.
          rewrite Env.elements_union. rewrite Env.elements_from_list. reflexivity.
          eapply NoDupMembers_idck, NoDupMembers_idty; eauto.
          intros ? Hin Hinlocs; eapply H5.
          eapply Env.In_from_list in Hinlocs; rewrite InMembers_idck, InMembers_idty in Hinlocs; eauto.
          eapply fst_InMembers, Env.In_Members; eauto.
    Qed.

  End ValidateBlock.

  Section ValidateGlobal.

    Definition check_env (env : list (ident * clock)) : bool :=
      forallb (check_clock (Env.from_list env)) (List.map snd env).

    Definition check_node {PSyn prefs} (G : @global PSyn prefs) (n : @node PSyn prefs) :=
      check_env (idck (idty (n_in n))) &&
      check_env (idck (idty (n_in n ++ n_out n))) &&
      check_block G (Env.from_list (idck (idty (n_in n ++ n_out n)))) (n_block n).

    Definition check_global {PSyn prefs} (G : @global PSyn prefs) :=
      check_nodup (List.map n_name G.(nodes)) &&
      (fix aux nds := match nds  with
                      | [] => true
                      | hd::tl => check_node (update G tl) hd && aux tl
                      end) G.(nodes).

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

    Lemma check_node_correct {PSyn prefs} : forall (G : @global PSyn prefs) n,
        check_node G n = true ->
        wc_node G n.
    Proof.
      intros * Hcheck.
      unfold check_node in Hcheck.
      repeat rewrite Bool.andb_true_iff in Hcheck. destruct Hcheck as ((Hc1&Hc2)&Hc3).
      repeat constructor.
      1-2:apply check_env_correct; auto.
      apply check_block_correct in Hc3.
      - eapply wc_block_incl; eauto.
        apply Env.elements_from_list_incl.
      - pose proof (n_nodup n) as (_&ND).
        eapply NoDupLocals_incl; eauto.
        rewrite <-map_fst_idty, <-map_fst_idck.
        apply incl_map, Env.elements_from_list_incl.
    Qed.

    Lemma check_global_correct {PSyn prefs} : forall (G : @global PSyn prefs),
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

  Lemma wc_exp_nclockof_In {PSyn prefs} : forall (G: @global PSyn prefs) vars e,
      wc_exp G vars e ->
      Forall (fun '(ck, o) => LiftO True (fun x => In (x, ck) vars) o) (nclockof e).
  Proof.
    induction e using exp_ind2; intros * Hwc;
      inv Hwc; simpl; repeat constructor; auto.
    1-6:rewrite Forall_map; eapply Forall_forall; intros; simpl; auto.
  Qed.

  Corollary wc_exps_nclocksof_In {PSyn prefs} : forall (G: @global PSyn prefs) vars es,
      Forall (wc_exp G vars) es ->
      Forall (fun '(ck, o) => LiftO True (fun x => In (x, ck) vars) o) (nclocksof es).
  Proof.
    intros * Hwc.
    unfold nclocksof. rewrite flat_map_concat_map. apply Forall_concat, Forall_map, Forall_forall; intros.
    repeat (take (Forall _ _) and eapply Forall_forall in it; eauto).
    eapply wc_exp_nclockof_In; eauto.
  Qed.

  Lemma wc_exp_clockof {PSyn prefs} : forall (G: @global PSyn prefs) vars e,
      wc_global G ->
      wc_env vars ->
      wc_exp G vars e ->
      Forall (wc_clock vars) (clockof e).
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
      simpl; unfold stripname; simpl; repeat constructor.
    - (* var *)
      simpl_list.
      unfold wc_env in Henv; rewrite Forall_forall in Henv.
      apply Henv in H0...
    - (* unop *)
      apply IHe in H1...
      rewrite H3 in H1; simpl in H1; inv H1; auto.
    - (* binop *)
      apply IHe1 in H3...
      rewrite H5 in H3. inv H3; auto.
    - (* fby *)
      rewrite Forall2_eq in H6, H7. rewrite H6.
      Forall_clocksof...
    - (* arrow *)
      rewrite Forall2_eq in H6, H7. rewrite H6.
      Forall_clocksof...
    - (* when *)
      destruct tys; [simpl in *; auto|].
      rewrite Forall_map. eapply Forall_forall; intros ? _.
      constructor...
      assert (Forall (wc_clock vars) (clocksof es)) as Hwc.
      { Forall_clocksof... }
      clear H.
      eapply Forall_Forall in H6...
      destruct (clocksof es); simpl in *; try congruence.
      inv H6. destruct H1; subst...
    - (* merge *)
      destruct es as [|(?&?)]; [simpl in *; auto; exfalso; auto|].
      inv H. inv H5. inv H6.
      assert (Forall (wc_clock vars) (clocksof l)) as Hwc.
      { Forall_clocksof... }
      clear H2.
      eapply Forall_Forall in H5...
      inv H7. simpl in *.
      destruct (clocksof l).
      1:{ destruct tys; simpl in *; auto; try congruence. }
      rewrite Forall_map. eapply Forall_forall; intros ? Hin.
      inv Hwc. inv H5. destruct H12; subst... inv H...
    - (* case *)
      apply IHe in H5.
      rewrite Forall_map. eapply Forall_forall; intros ? _...
      rewrite H6 in H5; inv H5...
    - (* app *)
      assert (Forall (wc_clock vars) (clocksof es)) as Hwc.
      { Forall_clocksof. }
      clear H.
      eapply wc_find_node in H7 as [G' Hwcnode]...
      assert (wc_clock vars bck) as Hbck.
      { eapply WellInstantiated_bck in H8...
        + rewrite <- clocksof_nclocksof in H8.
          rewrite Forall_forall in Hwc. apply Hwc in H8...
        + destruct Hwcnode as [? _]...
        + rewrite length_idck, length_idty. apply n_ingt0... }
      specialize (Forall2_app H8 H9) as Hinst.
      eapply WellInstantiated_wc_clocks in Hinst...
      + rewrite map_app, map_map, Forall_app in Hinst. destruct Hinst as [_ Hinst].
        rewrite Forall_map in Hinst. rewrite Forall_map.
        eapply Forall_impl; [|eauto].
        intros (?&?) ?; simpl in *. eapply wc_clock_incl...
        unfold anon_streams; rewrite map_filter_app.
        repeat rewrite <- app_assoc. repeat apply incl_app.
        * apply incl_refl.
        * eapply wc_exps_nclocksof_In in H5; eauto.
          intros ? Hmap. eapply map_filter_In' in Hmap as ((?&?)&Hin&?).
          eapply Forall_forall in H5; eauto; simpl in *.
          destruct o; simpl in *; auto; try congruence.
        * intros ? Hmap. eapply map_filter_In' in Hmap as ((?&?)&Hin&?).
          eapply in_map_iff in Hin as ((?&?)&Heq&?); inv Heq. congruence.
      + specialize (n_nodup n) as (Hndup&_).
        now rewrite fst_NoDupMembers, <-idck_app, <-idty_app, map_fst_idck, map_fst_idty, <-fst_NoDupMembers.
      + destruct Hwcnode as [_ [Hwcnode _]].
        rewrite <-idck_app, <-idty_app...
  Qed.

  Corollary wc_exp_clocksof {PSyn prefs} : forall (G: @global PSyn prefs) vars es,
      wc_global G ->
      wc_env vars ->
      Forall (wc_exp G vars) es ->
      Forall (wc_clock vars) (clocksof es).
  Proof with eauto.
    intros G vars es HwG Hwenv Hwc.
    unfold clocksof, nclocksof in *.
    rewrite flat_map_concat_map in *.
    rewrite <-Forall_concat, Forall_map.
    rewrite Forall_forall in *; intros.
    eapply wc_exp_clockof; eauto.
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

  Lemma WellInstantiated_is_free_in {PSyn prefs} : forall (G: @global PSyn prefs) f n inputs ins outs sub bck,
      wc_global G ->
      find_node f G = Some n ->
      Forall (fun '(ck, _) => forall x, Is_free_in_clock x ck -> In x inputs) ins ->
      Forall2 (WellInstantiated bck sub) (idck (idty (n_in n))) ins ->
      Forall2 (WellInstantiated bck sub) (idck (idty (n_out n))) outs ->
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
      - rewrite length_idck, length_idty. exact (n_ingt0 n). }

    specialize (Forall2_app Hwi1 Hwi2) as Hwi. clear Hwi1 Hwi2.
    rewrite <- idck_app in Hwi.

    assert (exists vars, Permutation (idck (idty (n_in n ++ n_out n))) vars /\ dep_ordered_on vars) as [vars [Hperm Hdepo]].
    { eapply wc_env_dep_ordered_on.
      - specialize (n_nodup n) as (Hndup&_).
        now rewrite NoDupMembers_idck, NoDupMembers_idty.
      - destruct Hwnode as [_ [? _]]; auto. }
    eapply Forall2_Permutation_1 in Hwi as [vars' [Hperm' Hwi]]. 2:rewrite <-idty_app; eauto.

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
    Context {PSyn1 PSyn2 : block -> Prop}.
    Context {prefs1 prefs2 : PS.t}.
    Variable G1 : @global PSyn1 prefs1.
    Variable G2 : @global PSyn2 prefs2.

    Hypothesis Heq : global_iface_eq G1 G2.

    Hint Constructors wc_exp.
    Fact iface_eq_wc_exp : forall vars e,
        wc_exp G1 vars e ->
        wc_exp G2 vars e.
    Proof with eauto.
      induction e using exp_ind2; intros Hwc; inv Hwc...
      1-5:econstructor; try (destruct Heq; erewrite <-equiv_program_enums)...
      1-8:rewrite Forall_forall in *...
      - intros ? Hin. specialize (H5 _ Hin). specialize (H _ Hin).
        rewrite Forall_forall in *...
      - intros ? Hin. specialize (H8 _ Hin). specialize (H _ Hin); simpl in H.
        rewrite Forall_forall in *...
      - intros ??; subst; simpl in *. specialize (H11 _ eq_refl).
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
    Proof with eauto.
      intros vars [xs es] Hwc.
      simpl in *. inv Hwc.
      2:econstructor; eauto; rewrite Forall_forall in *; eauto using iface_eq_wc_exp.
      (* app *)
      assert (Forall (wc_exp G2 vars) es0) as Hwt by (rewrite Forall_forall in *; eauto using iface_eq_wc_exp).
      assert (Forall (wc_exp G2 vars) er) as Hwt' by (rewrite Forall_forall in *; eauto using iface_eq_wc_exp).
      destruct Heq as (Hequiv&Heq'). specialize (Heq' f).
      remember (find_node f G2) as find.
      destruct Heq'.
      + congruence.
      + inv H3.
        destruct H as [? [? [? ?]]].
        econstructor...
        * rewrite <-H3...
        * rewrite <-H8...
    Qed.

    Fact iface_eq_wc_block : forall d vars,
        wc_block G1 vars d ->
        wc_block G2 vars d.
    Proof.
      induction d using block_ind2; intros * Hwc; inv Hwc.
      - constructor; auto using iface_eq_wc_equation.
      - econstructor; eauto using iface_eq_wc_exp.
        rewrite Forall_forall in *; eauto.
      - econstructor; eauto using iface_eq_wc_exp.
        do 2 (eapply Forall_forall; intros).
        repeat (take (Forall _ _) and eapply Forall_forall in it; eauto).
      - econstructor; eauto.
        rewrite Forall_forall in *; eauto.
    Qed.

    (* Lemma iface_eq_wc_node : forall n, *)
    (*     wc_node G1 n -> *)
    (*     wc_node G2 n. *)
    (* Proof. *)
    (*   intros n Hwt. *)
    (*   destruct Hwt as [? [? [? Hwc]]]. *)
    (*   repeat split; auto. *)
    (*   rewrite Forall_forall in *; intros. *)
    (*   eapply iface_eq_wc_block; eauto. *)
    (* Qed. *)

  End interface_eq.

  (** ** wc implies wl *)

  Hint Constructors wl_exp wl_block.

  Fact wc_exp_wl_exp {PSyn prefs} : forall (G: @global PSyn prefs) vars e,
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
    - (* arrow *)
      constructor; rewrite Forall_forall in *...
      + apply Forall2_length in H6. rewrite clocksof_annots in H6. repeat rewrite map_length in H6...
      + apply Forall2_length in H7. rewrite clocksof_annots in H7. repeat rewrite map_length in H7...
    - (* when *)
      constructor; rewrite Forall_forall in *...
      rewrite clocksof_annots, map_length in H7...
    - (* merge *)
      constructor...
      + rewrite Forall_forall in *...
        intros ? Hin. specialize (H _ Hin). specialize (H5 _ Hin).
        rewrite Forall_forall in *...
      + rewrite Forall_forall in *...
        intros. erewrite H7; eauto.
        rewrite clocksof_annots, map_length...
    - (* case *)
      constructor...
      + rewrite <- length_clockof_numstreams, H6...
      + rewrite Forall_forall in *...
        intros ? Hin. specialize (H _ Hin); simpl in H. specialize (H8 _ Hin).
        rewrite Forall_forall in *...
      + rewrite Forall_forall in *...
        intros. erewrite H10; eauto.
        rewrite clocksof_annots, map_length...
      + intros ??; subst; simpl in *.
        specialize (H11 _ eq_refl). rewrite Forall_forall in *...
      + intros ??; subst; simpl in *.
        specialize (H13 _ eq_refl).
        rewrite clocksof_annots, map_length in H13...
    - (* app *)
      econstructor...
      + rewrite Forall_forall in *...
      + rewrite Forall_forall in *...
      + eapply Forall_impl; [|eauto]. intros ? (?&Ck).
        rewrite <- length_clockof_numstreams, Ck...
      + apply Forall2_length in H8.
        rewrite length_idck, length_idty, length_nclocksof_annots in H8...
      + apply Forall2_length in H9.
        rewrite length_idck, length_idty, map_length in H9...
  Qed.
  Hint Resolve wc_exp_wl_exp.

  Corollary Forall_wc_exp_wl_exp {PSyn prefs} : forall (G: @global PSyn prefs) vars es,
      Forall (wc_exp G vars) es ->
      Forall (wl_exp G) es.
  Proof. intros. rewrite Forall_forall in *; eauto. Qed.
  Hint Resolve Forall_wc_exp_wl_exp.

  Fact wc_equation_wl_equation {PSyn prefs} : forall (G: @global PSyn prefs) vars equ,
      wc_equation G vars equ ->
      wl_equation G equ.
  Proof with eauto.
    intros G vars [xs es] Heq.
    inv Heq; econstructor; simpl; eauto.
    - repeat econstructor; eauto.
      + eapply Forall_impl; [|eauto]. intros ? (?&Ck).
        rewrite <- length_clockof_numstreams, Ck...
      + apply Forall2_length in H4.
        rewrite length_idck, length_idty, length_nclocksof_annots in H4...
      + apply Forall3_length in H5 as (Hlen1&Hlen2).
        rewrite length_idck, length_idty, map_length in Hlen1...
    - rewrite app_nil_r. apply Forall2_length in H7. now rewrite map_length in H7.
    - apply Forall2_length in H2. now rewrite length_clocksof_annots in H2.
  Qed.
  Hint Resolve wc_equation_wl_equation.

  Fact wc_block_wl_block {PSyn prefs} : forall (G: @global PSyn prefs) d vars,
      wc_block G vars d ->
      wl_block G d.
  Proof.
    induction d using block_ind2; intros * Wc; inv Wc; eauto.
    1-3:econstructor; eauto.
    - rewrite Forall_forall in *; intros; eauto.
    - now rewrite <-length_clockof_numstreams, H5.
    - now rewrite <-length_clockof_numstreams, H3.
    - do 2 (eapply Forall_forall; intros).
      repeat (take (Forall _ _) and eapply Forall_forall in it; eauto).
    - rewrite Forall_forall in *; intros; eauto.
  Qed.
  Hint Resolve wc_block_wl_block.

  Fact wc_node_wl_node {PSyn prefs} : forall (G: @global PSyn prefs) n,
      wc_node G n ->
      wl_node G n.
  Proof with eauto.
    intros G n [_ [_ Hwc]].
    unfold wl_node...
  Qed.
  Hint Resolve wc_node_wl_node.

  Fact wc_global_wl_global {PSyn prefs} : forall (G: @global PSyn prefs),
      wc_global G ->
      wl_global G.
  Proof with eauto.
    intros G Hwt.
    unfold wc_global, wl_global, wt_program in *.
    induction Hwt; constructor...
    destruct H...
  Qed.
  Hint Resolve wc_global_wl_global.

  (** ** wc implies wx *)

  Hint Constructors wx_exp wl_block.

  Fact wc_exp_wx_exp {PSyn prefs} (G: @global PSyn prefs) : forall vars e,
      wc_exp G vars e ->
      wx_exp (map fst vars) e.
  Proof with eauto.
    induction e using exp_ind2; intro Hwt; inv Hwt; auto.
    - (* var *)
      constructor...
      eapply in_map_iff. now do 2 esplit; eauto.
    - (* fby *)
      constructor; rewrite Forall_forall in *...
    - (* arrow *)
      constructor; rewrite Forall_forall in *...
    - (* when *)
      constructor; rewrite Forall_forall in *...
      eapply in_map_iff. now do 2 esplit; eauto.
    - (* merge *)
      constructor...
      + eapply in_map_iff. now do 2 esplit; eauto.
      + rewrite Forall_forall in *...
        intros ? Hin. specialize (H _ Hin). specialize (H5 _ Hin).
        rewrite Forall_forall in *...
    - (* case *)
      constructor...
      + rewrite Forall_forall in *...
        intros ? Hin. specialize (H _ Hin); simpl in H. specialize (H8 _ Hin).
        rewrite Forall_forall in *...
      + intros ??; subst; simpl in *.
        specialize (H11 _ eq_refl). rewrite Forall_forall in *...
    - (* app *)
      econstructor...
      + rewrite Forall_forall in *...
      + rewrite Forall_forall in *...
  Qed.
  Hint Resolve wc_exp_wx_exp.

  Corollary Forall_wc_exp_wx_exp {PSyn prefs} (G: @global PSyn prefs) : forall vars es,
      Forall (wc_exp G vars) es ->
      Forall (wx_exp (map fst vars)) es.
  Proof. intros. rewrite Forall_forall in *; eauto. Qed.
  Hint Resolve Forall_wc_exp_wx_exp.

  Fact wc_equation_wx_equation {PSyn prefs} (G: @global PSyn prefs) : forall vars equ,
      wc_equation G vars equ ->
      wx_equation (map fst vars) equ.
  Proof with eauto.
    intros vars [xs es] Heq. inv Heq; repeat constructor; eauto.
    + intros ? Hin.
      eapply Forall2_ignore2, Forall_forall in H7 as (?&_&Hin'); eauto.
      eapply in_map_iff. now do 2 esplit; eauto.
    + intros ? Hin.
      eapply Forall2_ignore2, Forall_forall in H2 as (?&_&Hin'); eauto.
      eapply in_map_iff. now do 2 esplit; eauto.
  Qed.
  Hint Resolve wc_equation_wx_equation.

  Fact wc_block_wx_block {PSyn prefs} (G: @global PSyn prefs) : forall blk vars,
      wc_block G vars blk ->
      wx_block (map fst vars) blk.
  Proof.
    induction blk using block_ind2; intros * Wc; inv Wc; eauto.
    1-4:econstructor; eauto.
    1,3:rewrite Forall_forall in *; intros; eauto.
    - rewrite <-map_fst_idty, <-map_fst_idck, <-map_app; eauto.
    - do 2 (eapply Forall_forall; intros).
      repeat (take (Forall _ _) and eapply Forall_forall in it; eauto).
      eapply wx_block_incl; eauto using incl_map.
      intros ? Hin. eapply in_map_iff in Hin as ((?&?)&?&Hin); subst.
      eapply H6 in Hin as (Hin&?); subst.
      eapply in_map_iff; do 2 esplit; [|eauto]. eauto.
  Qed.
  Hint Resolve wc_block_wx_block.

  Fact wc_node_wx_node {PSyn prefs} : forall (G: @global PSyn prefs) n,
      wc_node G n ->
      wx_node n.
  Proof with eauto.
    intros G n [_ [_ Hwc]].
    unfold wx_node.
    rewrite <-map_fst_idty, <-map_fst_idck...
  Qed.
  Hint Resolve wc_node_wx_node.

  Fact wc_global_wx_global {PSyn prefs} : forall (G: @global PSyn prefs),
      wc_global G ->
      wx_global G.
  Proof with eauto.
    intros G Hwc.
    unfold wc_global, wx_global, wt_program, units in *; simpl in *.
    induction Hwc...
    destruct H...
  Qed.
  Hint Resolve wc_global_wx_global.

  (** Additional properties *)

  Lemma wc_block_Is_defined_in {PSyn prefs} (G: @global PSyn prefs) : forall blk env x,
      wc_block G env blk ->
      Is_defined_in x blk ->
      InMembers x env.
  Proof.
    induction blk using block_ind2; intros * Hwc Hdef; inv Hwc; inv Hdef.
    - (* equation *)
      inv H1; auto.
      + rename H9 into Hwc.
        eapply Forall2_ignore2, Forall_forall in Hwc as (?&_&Hin); eauto using In_InMembers.
      + rename H4 into Hwc.
        eapply Forall2_ignore2, Forall_forall in Hwc as (?&_&Hin); eauto using In_InMembers.
    - (* reset *)
      eapply Exists_exists in H1 as (?&Hin1&Hdef).
      repeat (take (Forall _ _) and eapply Forall_forall in it; eauto).
    - (* switch *)
      rename H1 into Hdef. do 2 (eapply Exists_exists in Hdef as (?&?&Hdef)).
      repeat (take (Forall _ _) and eapply Forall_forall in it; eauto).
      eapply it in it0; eauto.
      eapply InMembers_In in it0 as (?&Hin). eapply H6 in Hin as (Hin&_); eauto using In_InMembers.
    - (* local *)
      eapply Exists_exists in H2 as (?&Hin1&Hdef).
      repeat (take (Forall _ blocks) and eapply Forall_forall in it; eauto).
      eapply it in it0; eauto.
      apply InMembers_app in it0 as [|Hin]; auto.
      exfalso. rewrite InMembers_idck, InMembers_idty in Hin. eauto.
  Qed.

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
