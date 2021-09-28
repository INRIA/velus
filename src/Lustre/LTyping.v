From Velus Require Import Common.
From Velus Require Import CommonProgram.
From Velus Require Import CommonTyping.
From Velus Require Import Operators.
From Velus Require Import Clocks.
From Velus Require Import Lustre.LSyntax.

From Coq Require Import List Sorting Orders.
Import List.ListNotations.
Open Scope list_scope.

From Coq Require Import Morphisms.

From Velus Require Import Environment.
From Velus Require Import Operators.

(** * Lustre typing *)

(**

  Typing judgements for Lustre.
  Classify Lustre programs which are statically well-formed.

 *)

Module Type LTYPING
       (Import Ids   : IDS)
       (Import Op    : OPERATORS)
       (Import OpAux : OPERATORS_AUX Ids Op)
       (Import Cks   : CLOCKS Ids Op OpAux)
       (Import Syn   : LSYNTAX Ids Op OpAux Cks).

  (** ** Clocks *)
  Section WellTyped.

    Variable enums : list (ident * nat).
    Variable Γ     : list (ident * type).

    Inductive wt_clock : clock -> Prop :=
    | wt_Cbase:
        wt_clock Cbase
    | wt_Con: forall ck x tn c,
        In (x, Tenum tn) Γ ->
        In tn enums ->
        c < snd tn ->
        wt_clock ck ->
        wt_clock (Con ck x (Tenum tn, c)).

    Inductive wt_nclock : nclock -> Prop :=
    | wt_Cnamed: forall id ck,
        wt_clock ck ->
        wt_nclock (ck, id).

  End WellTyped.

  Import Permutation.

  (** ** Expressions and equations *)
  Section WellTyped.
    Context {PSyn : block -> Prop}.
    Context {prefs : PS.t}.

    Variable G     : @global PSyn prefs.
    Variable Γ     : list (ident * type).

    Definition wt_enum ty : Prop :=
      match ty with
      | Tenum tn => In tn G.(enums) /\ (0 < snd tn)
      | _ => True
      end.

    Inductive wt_exp : exp -> Prop :=
    | wt_Econst: forall c,
        wt_exp (Econst c)

    | wt_Eenum: forall k tn,
        In tn G.(enums) ->
        k < snd tn ->
        wt_exp (Eenum k (Tenum tn))

    | wt_Evar: forall x ty nck,
        In (x, ty) Γ ->
        wt_nclock G.(enums) Γ nck ->
        wt_exp (Evar x (ty, nck))

    | wt_Eunop: forall op e tye ty nck,
        wt_exp e ->
        typeof e = [tye] ->
        type_unop op tye = Some ty ->
        wt_enum ty ->
        wt_nclock G.(enums) Γ nck ->
        wt_exp (Eunop op e (ty, nck))

    | wt_Ebinop: forall op e1 e2 ty1 ty2 ty nck,
        wt_exp e1 ->
        wt_exp e2 ->
        typeof e1 = [ty1] ->
        typeof e2 = [ty2] ->
        type_binop op ty1 ty2 = Some ty ->
        wt_enum ty ->
        wt_nclock G.(enums) Γ nck ->
        wt_exp (Ebinop op e1 e2 (ty, nck))

    | wt_Efby: forall e0s es anns,
        Forall wt_exp e0s ->
        Forall wt_exp es ->
        typesof es = map fst anns ->
        typesof e0s = map fst anns ->
        Forall (wt_nclock G.(enums) Γ) (map snd anns) ->
        wt_exp (Efby e0s es anns)

    | wt_Earrow: forall e0s es anns,
        Forall wt_exp e0s ->
        Forall wt_exp es ->
        typesof es = map fst anns ->
        typesof e0s = map fst anns ->
        Forall (wt_nclock G.(enums) Γ) (map snd anns) ->
        wt_exp (Earrow e0s es anns)

    | wt_Ewhen: forall es x b tn tys nck,
        In (x, Tenum tn) Γ ->
        In tn G.(enums) ->
        b < snd tn ->
        Forall wt_exp es ->
        typesof es = tys ->
        wt_nclock G.(enums) Γ nck ->
        wt_exp (Ewhen es x b (tys, nck))

    | wt_Emerge: forall x tn es tys nck,
        In (x, Tenum tn) Γ ->
        In tn G.(enums) ->
        Permutation (map fst es) (seq 0 (snd tn)) ->
        es <> nil ->
        Forall (fun es => Forall wt_exp (snd es)) es ->
        Forall (fun es => typesof (snd es) = tys) es ->
        wt_nclock G.(enums) Γ nck ->
        wt_exp (Emerge (x, Tenum tn) es (tys, nck))

    | wt_EcaseTotal: forall e es tn tys nck,
        wt_exp e ->
        typeof e = [Tenum tn] ->
        In tn G.(enums) ->
        Permutation (map fst es) (seq 0 (snd tn)) ->
        es <> nil ->
        Forall (fun es => Forall wt_exp (snd es)) es ->
        Forall (fun es => typesof (snd es) = tys) es ->
        wt_nclock G.(enums) Γ nck ->
        wt_exp (Ecase e es None (tys, nck))

    | wt_EcaseDefault: forall e es d tn tys nck,
        wt_exp e ->
        typeof e = [Tenum tn] ->
        In tn G.(enums) ->
        incl (map fst es) (seq 0 (snd tn)) ->
        NoDupMembers es ->
        es <> nil ->
        Forall (fun es => Forall wt_exp (snd es)) es ->
        Forall (fun es => typesof (snd es) = tys) es ->
        Forall wt_exp d ->
        typesof d = tys ->
        wt_nclock G.(enums) Γ nck ->
        wt_exp (Ecase e es (Some d) (tys, nck))

    | wt_Eapp: forall f es er anns n,
        Forall wt_exp es ->
        Forall wt_exp er ->
        find_node f G = Some n ->
        Forall2 (fun et '(_, (t, _, _)) => et = t) (typesof es) n.(n_in) ->
        Forall2 (fun a '(_, (t, _, _)) => fst a = t) anns n.(n_out) ->
        Forall (fun e => typeof e = [bool_velus_type]) er ->
        Forall (fun a => wt_nclock G.(enums) (Γ++(idty (fresh_ins es++anon_streams anns))) (snd a)) anns ->
        wt_exp (Eapp f es er anns).

    Definition wt_equation (eq : equation) : Prop :=
      let (xs, es) := eq in
      Forall wt_exp es
      /\ Forall2 (fun x ty=> In (x, ty) Γ) xs (typesof es).

  End WellTyped.

  Definition wt_clocks enums (Γ : list (ident * type)) : list (ident * (type * clock * ident)) -> Prop :=
    Forall (fun '(_, (_, ck, _)) => wt_clock enums Γ ck).

  Inductive wt_block {PSyn prefs} (G: @global PSyn prefs) : list (ident * type) -> block -> Prop :=
  | wt_Beq: forall env eq,
      wt_equation G env eq ->
      wt_block G env (Beq eq)
  | wt_Breset: forall env blocks er,
      Forall (wt_block G env) blocks ->
      wt_exp G env er ->
      typeof er = [bool_velus_type] ->
      wt_block G env (Breset blocks er)
  | wt_Blocal: forall env locs blocks,
      Forall (wt_block G (env ++ idty (idty locs))) blocks ->
      wt_clocks G.(enums) (env ++ idty (idty locs)) locs ->
      Forall (wt_enum G) (map snd (idty (idty locs))) ->
      wt_block G env (Blocal locs blocks).

  Definition wt_node {PSyn prefs} (G: @global PSyn prefs) (n: @node PSyn prefs) : Prop
    :=    wt_clocks G.(enums) (idty (idty n.(n_in))) n.(n_in)
       /\ wt_clocks G.(enums) (idty (idty (n.(n_in) ++ n.(n_out)))) n.(n_out)
       /\ Forall (wt_enum G) (map snd (idty (idty (n.(n_in) ++ n.(n_out)))))
       /\ wt_block G (idty (idty (n.(n_in) ++ n.(n_out)))) n.(n_block).

  Definition wt_global {PSyn prefs} (G: @global PSyn prefs) : Prop :=
    In (bool_id, 2) G.(enums) /\
    wt_program wt_node G.

  Hint Constructors wt_clock wt_nclock wt_exp wt_block : ltyping.
  Hint Unfold wt_equation : ltyping.

  Section wt_exp_ind2.
    Context (PSyn : block -> Prop).
    Context (prefs : PS.t).

    Variable (G : @global PSyn prefs).
    Variable Γ : list (ident * type).
    Variable P : exp -> Prop.

    Hypothesis EconstCase:
      forall c,
        P (Econst c).

    Hypothesis EenumCase:
      forall k tn,
        In tn G.(enums) ->
        k < snd tn ->
        P (Eenum k (Tenum tn)).

    Hypothesis EvarCase:
      forall x ty nck,
        In (x, ty) Γ ->
        wt_nclock G.(enums) Γ nck ->
        P (Evar x (ty, nck)).

    Hypothesis EunopCase:
      forall op e tye ty nck,
        wt_exp G Γ e ->
        P e ->
        typeof e = [tye] ->
        type_unop op tye = Some ty ->
        wt_enum G ty ->
        wt_nclock G.(enums) Γ nck ->
        P (Eunop op e (ty, nck)).

    Hypothesis EbinopCase:
      forall op e1 e2 ty1 ty2 ty nck,
        wt_exp G Γ e1 ->
        P e1 ->
        wt_exp G Γ e2 ->
        P e2 ->
        typeof e1 = [ty1] ->
        typeof e2 = [ty2] ->
        type_binop op ty1 ty2 = Some ty ->
        wt_enum G ty ->
        wt_nclock G.(enums) Γ nck ->
        P (Ebinop op e1 e2 (ty, nck)).

    Hypothesis EfbyCase:
      forall e0s es anns,
        Forall (wt_exp G Γ) e0s ->
        Forall (wt_exp G Γ) es ->
        Forall P e0s ->
        Forall P es ->
        typesof es = map fst anns ->
        typesof e0s = map fst anns ->
        Forall (wt_nclock G.(enums) Γ) (map snd anns) ->
        P (Efby e0s es anns).

    Hypothesis EarrowCase:
      forall e0s es anns,
        Forall (wt_exp G Γ) e0s ->
        Forall (wt_exp G Γ) es ->
        Forall P e0s ->
        Forall P es ->
        typesof es = map fst anns ->
        typesof e0s = map fst anns ->
        Forall (wt_nclock G.(enums) Γ) (map snd anns) ->
        P (Earrow e0s es anns).

    Hypothesis EwhenCase:
      forall es x b tn tys nck,
        In (x, Tenum tn) Γ ->
        In tn G.(enums) ->
        b < snd tn ->
        Forall (wt_exp G Γ) es ->
        Forall P es ->
        typesof es = tys ->
        wt_nclock G.(enums) Γ nck ->
        P (Ewhen es x b (tys, nck)).

    Hypothesis EmergeCase:
      forall x es tn tys nck,
        In (x, Tenum tn) Γ ->
        In tn G.(enums) ->
        Permutation (map fst es) (seq 0 (snd tn)) ->
        es <> nil ->
        Forall (fun es => Forall (wt_exp G Γ) (snd es)) es ->
        Forall (fun es => Forall P (snd es)) es ->
        Forall (fun es => typesof (snd es) = tys) es ->
        wt_nclock G.(enums) Γ nck ->
        P (Emerge (x, Tenum tn) es (tys, nck)).

    Hypothesis EcasetotalCase:
      forall e es tn tys nck,
        wt_exp G Γ e ->
        P e ->
        typeof e = [Tenum tn] ->
        In tn G.(enums) ->
        Permutation (map fst es) (seq 0 (snd tn)) ->
        es <> nil ->
        Forall (fun es => Forall (wt_exp G Γ) (snd es)) es ->
        Forall (fun es => Forall P (snd es)) es ->
        Forall (fun es => typesof (snd es) = tys) es ->
        (* Forall (wt_exp G Γ) d -> *)
        (* Forall P d -> *)
        (* typesof d = tys -> *)
        wt_nclock G.(enums) Γ nck ->
        P (Ecase e es None (tys, nck)).

    Hypothesis EcasedefaultCase:
      forall e es d tn tys nck,
        wt_exp G Γ e ->
        P e ->
        typeof e = [Tenum tn] ->
        In tn G.(enums) ->
        incl (map fst es) (seq 0 (snd tn)) ->
        NoDupMembers es ->
        es <> nil ->
        Forall (fun es => Forall (wt_exp G Γ) (snd es)) es ->
        Forall (fun es => Forall P (snd es)) es ->
        Forall (fun es => typesof (snd es) = tys) es ->
        Forall (wt_exp G Γ) d ->
        Forall P d ->
        typesof d = tys ->
        wt_nclock G.(enums) Γ nck ->
        P (Ecase e es (Some d) (tys, nck)).

    Hypothesis EappCase:
      forall f es er anns n,
        Forall (wt_exp G Γ) es ->
        Forall (wt_exp G Γ) er ->
        Forall P es ->
        Forall P er ->
        find_node f G = Some n ->
        Forall2 (fun et '(_, (t, _, _)) => et = t) (typesof es) n.(n_in) ->
        Forall2 (fun a '(_, (t, _, _)) => fst a = t) anns n.(n_out) ->
        Forall (fun e => typeof e = [bool_velus_type]) er ->
        Forall (fun a => wt_nclock G.(enums) (Γ++(idty (fresh_ins es++anon_streams anns))) (snd a)) anns ->
        P (Eapp f es er anns).

    Fixpoint wt_exp_ind2 (e: exp) (H: wt_exp G Γ e) {struct H} : P e.
    Proof.
      destruct H; eauto.
      - apply EfbyCase; auto.
        + clear H2. induction H; auto.
        + clear H1. induction H0; auto.
      - apply EarrowCase; auto.
        + clear H2. induction H; auto.
        + clear H1. induction H0; auto.
      - eapply EwhenCase; eauto.
        clear H3. induction H2; auto.
      - apply EmergeCase; auto.
        clear H1 H2 H4.
        induction H3; constructor; auto.
        induction H1; auto.
      - eapply EcasetotalCase; eauto.
        clear H2 H3 H5.
        induction H4; constructor; auto.
        induction H2; auto.
      - eapply EcasedefaultCase; eauto.
        + clear H2 H3 H4 H6.
          induction H5; constructor; auto.
          induction H2; auto.
        + clear H8.
          induction H7; auto.
      - eapply EappCase; eauto.
        + clear H2 H5. induction H; eauto.
        + clear H4. induction H0; eauto.
    Qed.

  End wt_exp_ind2.

  Lemma wt_global_NoDup {PSyn prefs}:
    forall (g : @global PSyn prefs),
      wt_global g ->
      NoDup (map name (nodes g)).
  Proof.
    intros * (?&Wt).
    eapply wt_program_NoDup in Wt; eauto.
  Qed.

  Lemma wt_find_node {PSyn prefs}:
    forall (G : @global PSyn prefs) f n,
      wt_global G ->
      find_node f G = Some n ->
      exists G', wt_node G' n /\ enums G' = enums G.
  Proof.
    intros G f n' (?&Hwt) Hfind.
    apply option_map_inv in Hfind as ((?&?)&(?&?)); subst.
    eapply wt_program_find_unit' in Hwt as (?&?&Hequiv); [|eauto].
    eexists; split; eauto.
    apply equiv_program_enums in Hequiv; auto.
  Qed.

  Lemma wt_clock_add:
    forall x v enums env ck,
      ~InMembers x env ->
      wt_clock enums env ck ->
      wt_clock enums ((x, v) :: env) ck.
  Proof.
    induction ck; auto with ltyping.
    inversion 2.
    auto with ltyping datatypes.
  Qed.

  Instance wt_clock_Proper enums:
    Proper (@Permutation.Permutation (ident * type) ==> @eq clock ==> iff)
           (wt_clock enums).
  Proof.
    intros env' env Henv ck' ck Hck.
    rewrite Hck; clear Hck ck'.
    induction ck.
    - split; auto with ltyping.
    - destruct IHck.
      split; inversion_clear 1; constructor;
        try rewrite Henv in *;
        auto with ltyping.
  Qed.

  Instance wt_clock_enums_Proper :
    Proper (@incl _ ==> @eq _ ==> @eq _ ==> Basics.impl) wt_clock.
  Proof.
    intros ?? Same ??? ? ck ? Wt; subst.
    induction ck; inversion_clear Wt; subst; repeat constructor; auto.
  Qed.

  Instance wt_nclock_Proper enums:
    Proper (@Permutation.Permutation (ident * type) ==> @eq nclock ==> iff)
           (wt_nclock enums).
  Proof.
    intros env' env Henv ck' ck Hck.
    rewrite Hck; clear Hck ck'.
    destruct ck;
      split; inversion 1;
        (rewrite Henv in * || rewrite <-Henv in * || idtac);
        auto with ltyping.
  Qed.

  Instance wt_nclock_pointwise_Proper enums :
    Proper (@Permutation.Permutation (ident * type)
                                     ==> pointwise_relation nclock iff)
           (wt_nclock enums).
  Proof.
    intros env' env Henv e.
    now rewrite Henv.
  Qed.

  Instance wt_nclock_incl_Proper :
    Proper (@incl _ ==> @eq _ ==> @eq _ ==> Basics.impl) wt_nclock.
  Proof.
    intros ?? Same ??? ? (ck&?) ? Wt; subst.
    inv Wt. constructor.
    rewrite Same in H0; auto.
  Qed.

  Instance wt_exp_Proper {PSyn prefs}:
    Proper (@eq (@global PSyn prefs) ==> @Permutation.Permutation (ident * type)
                ==> @eq exp ==> iff)
           wt_exp.
  Proof.
    intros G G' HG env' env Henv e' e He.
    rewrite HG, He. clear HG He.
    split; intro H;
      induction H using wt_exp_ind2;
      (rewrite Henv in * || rewrite <-Henv in * || idtac);
      try match goal with
          | H:Forall (fun a => wt_nclock _ (env' ++ _) (snd a)) _ |- _ =>
            setoid_rewrite Henv in H
          | H:Forall (fun a => wt_nclock _ (env ++ _) (snd a)) _ |- _ =>
            setoid_rewrite <-Henv in H
          end;
      eauto with ltyping;
      econstructor; eauto.
  Qed.

  Instance wt_exp_pointwise_Proper {PSyn prefs}:
    Proper (@eq (@global PSyn prefs) ==> @Permutation.Permutation (ident * type)
                                     ==> pointwise_relation exp iff) wt_exp.
  Proof.
    intros G G' HG env' env Henv e.
    now rewrite HG, Henv.
  Qed.

  Instance wt_equation_Proper {PSyn prefs}:
    Proper (@eq (@global PSyn prefs) ==> @Permutation.Permutation (ident * type)
                ==> @eq equation ==> iff)
           wt_equation.
  Proof.
    intros G1 G2 HG env1 env2 Henv eq1 eq2 Heq.
    rewrite Heq, HG. destruct eq2 as (xs & es).
    unfold wt_equation. rewrite Henv.
    split; intro WTeq; destruct WTeq as (WTeq1 & WTeq2); split; auto.
    - apply Forall2_forall; split;
        eauto using Forall2_length.
      apply Forall2_combine in WTeq2.
      intros * Hin.
      apply Forall_forall with (1:=WTeq2) in Hin.
      now rewrite Henv in Hin.
    - apply Forall2_forall; split;
        eauto using Forall2_length.
      apply Forall2_combine in WTeq2.
      intros * Hin.
      apply Forall_forall with (1:=WTeq2) in Hin.
      now rewrite <-Henv in Hin.
  Qed.

  (** Adding variables to the environment preserves typing *)

  Section incl.

    Fact wt_clock_incl : forall enums vars vars' cl,
      incl vars vars' ->
      wt_clock enums vars cl ->
      wt_clock enums vars' cl.
    Proof.
      intros * Hincl Hwt.
      induction Hwt.
      - constructor.
      - constructor; auto.
    Qed.
    Local Hint Resolve wt_clock_incl.

    Fact wt_nclock_incl : forall enums vars vars' cl,
        incl vars vars' ->
        wt_nclock enums vars cl ->
        wt_nclock enums vars' cl.
    Proof.
      intros * Hincl Hwt.
      destruct Hwt; constructor; eauto.
    Qed.
    Local Hint Resolve wt_nclock_incl.

    Lemma wt_exp_incl {PSyn prefs} : forall (G: @global PSyn prefs) vars vars' e,
        incl vars vars' ->
        wt_exp G vars e ->
        wt_exp G vars' e.
    Proof.
      intros * Hincl Hwt.
      induction Hwt using wt_exp_ind2;
        econstructor; eauto.
      1-2:eapply Forall_impl; [| eauto]; intros; eauto.
      (* app *)
      eapply Forall_impl; [| eauto].
      intros; simpl in *; eauto.
      eapply wt_nclock_incl; eauto.
      eapply incl_appl'; eauto.
    Qed.

    Lemma wt_equation_incl {PSyn prefs} : forall (G: @global PSyn prefs) vars vars' eq,
        incl vars vars' ->
        wt_equation G vars eq ->
        wt_equation G vars' eq.
    Proof.
      intros * Hincl Hwt.
      destruct eq; simpl in *. destruct Hwt as [Hwt1 Hwt2].
      split.
      - eapply Forall_impl; [| eauto].
        intros. eapply wt_exp_incl; eauto.
      - eapply Forall2_impl_In; [| eauto].
        intros; simpl in H1. eauto.
    Qed.

    Lemma wt_block_incl {PSyn prefs} : forall (G: @global PSyn prefs) d vars vars',
        incl vars vars' ->
        wt_block G vars d ->
        wt_block G vars' d .
    Proof.
      induction d using block_ind2; intros * Incl Wt; inv Wt.
      - constructor. eauto using wt_equation_incl.
      - econstructor; eauto using wt_exp_incl.
        eapply Forall_Forall in H; eauto. clear H2.
        eapply Forall_impl; [|eauto]; intros ? (?&?); eauto.
      - constructor; auto.
        + rewrite Forall_forall in *; intros.
          eapply H; eauto using incl_appl'.
        + eapply Forall_impl; [|eauto]; intros (?&(?&?)&?) ?.
          eapply wt_clock_incl; [|eauto]; auto using incl_appl'.
    Qed.

  End incl.

  Local Hint Resolve wt_clock_incl incl_appl incl_refl.
  Lemma wt_exp_clockof {PSyn prefs}:
    forall (G: @global PSyn prefs) env e,
      wt_exp G env e ->
      Forall (wt_clock G.(enums) (env++idty (fresh_in e))) (clockof e).
  Proof.
    intros * Hwt.
    apply Forall_forall. intros ck Hin.
    inv Hwt; simpl in *.
    - destruct Hin as [Hin|]; [|contradiction].
      rewrite <-Hin; auto with ltyping.
    - destruct Hin as [Hin|]; [|contradiction].
      rewrite <-Hin; auto with ltyping.
    - destruct Hin as [Hin|]; [|contradiction].
      rewrite <-Hin.
      destruct nck; unfold clock_of_nclock; simpl in *;
        match goal with H:wt_nclock _ _ _ |- _ => inv H end.
      rewrite app_nil_r; auto.
    - destruct Hin as [Hin|]; [|contradiction].
      rewrite <-Hin.
      destruct nck; unfold clock_of_nclock; simpl in *;
        match goal with H:wt_nclock _ _ _ |- _ => inv H end; eauto.
    - destruct Hin as [Hin|]; [|contradiction].
      rewrite <-Hin.
      destruct nck; unfold clock_of_nclock; simpl in *;
        match goal with H:wt_nclock _ _ _ |- _ => inv H end; eauto.
    - match goal with H:Forall (wt_nclock _ _) _ |- _ =>
                      rewrite Forall_map in H end.
      apply in_map_iff in Hin.
      destruct Hin as ((ty & nck) & Hck & Hin).
      apply Forall_forall with (1:=H3) in Hin.
      destruct nck; unfold clock_of_nclock in *; simpl in *; subst;
        match goal with H:wt_nclock _ _ _ |- _ => inv H end; eauto.
    - match goal with H:Forall (wt_nclock _ _) _ |- _ =>
                      rewrite Forall_map in H end.
      apply in_map_iff in Hin.
      destruct Hin as ((ty & nck) & Hck & Hin).
      apply Forall_forall with (1:=H3) in Hin.
      destruct nck; unfold clock_of_nclock in *; simpl in *; subst;
        match goal with H:wt_nclock _ _ _ |- _ => inv H end; eauto.
    - destruct nck; unfold clock_of_nclock in *; simpl in *;
        apply in_map_iff in Hin; destruct Hin as (? & Hs & Hin); subst;
          match goal with H:wt_nclock _ _ _ |- _ => inv H end; eauto.
    - destruct nck; unfold clock_of_nclock in *; simpl in *;
        apply in_map_iff in Hin; destruct Hin as (? & Hs & Hin); subst;
          match goal with H:wt_nclock _ _ _ |- _ => inv H end; eauto.
    - destruct nck; unfold clock_of_nclock in *; simpl in *;
        apply in_map_iff in Hin; destruct Hin as (? & Hs & Hin); subst;
          match goal with H:wt_nclock _ _ _ |- _ => inv H end; eauto.
    - destruct nck; unfold clock_of_nclock in *; simpl in *;
        apply in_map_iff in Hin; destruct Hin as (? & Hs & Hin); subst;
          match goal with H:wt_nclock _ _ _ |- _ => inv H end; eauto.
    - apply in_map_iff in Hin.
      destruct Hin as (x & Hs & Hin).
      match goal with H:Forall _ anns |- _ =>
                      apply Forall_forall with (1:=H) in Hin end.
      destruct x as (ty, nck).
      destruct nck; unfold clock_of_nclock in *; simpl in *;
        subst; match goal with H:wt_nclock _ _ _ |- _ => inv H end.
      eapply wt_clock_incl; [| eauto].
      eapply incl_appr'. unfold idty; repeat rewrite map_app.
      eapply incl_appr'. eapply incl_appr. reflexivity.
  Qed.

  (** ** Validation *)

  Fixpoint check_clock (eenv : Env.t nat) (venv : Env.t type) (ck : clock) : bool :=
    match ck with
    | Cbase => true
    | Con ck' x (ty, k) =>
      match Env.find x venv with
      | Some (Tenum (xt, n)) => (ty ==b Tenum(xt, n))
                              && match Env.find xt eenv with
                                 | None => false
                                 | Some n' => (n' ==b n) && (k <? n) && check_clock eenv venv ck'
                                 end
      | _ => false
      end
    end.

  Definition check_nclock (eenv : Env.t nat) (venv : Env.t type) (nck : nclock) : bool :=
    check_clock eenv venv (fst nck).

  Lemma check_clock_correct:
    forall eenv venv ck,
      check_clock eenv venv ck = true ->
      wt_clock (Env.elements eenv) (Env.elements venv) ck.
  Proof.
    induction ck; intro CC. now constructor.
    simpl in CC. cases_eqn Heq; subst.
    - repeat rewrite Bool.andb_true_iff in CC; destruct CC as (CC1 & (CC2 & CC3) & CC4).
      apply IHck in CC4. rewrite equiv_decb_equiv in CC1; inv CC1.
      rewrite equiv_decb_equiv in CC2; inv CC2.
      apply Env.elements_correct in Heq0. apply Env.elements_correct in Heq3.
      apply Nat.ltb_lt in CC3.
      constructor; auto.
    - rewrite Bool.andb_false_r in CC. congruence.
  Qed.

  Lemma check_nclock_correct:
    forall eenv venv nck,
      check_nclock eenv venv nck = true ->
      wt_nclock (Env.elements eenv) (Env.elements venv) nck.
  Proof.
    destruct nck as (n, ck).
    intro CC; now apply check_clock_correct in CC.
  Qed.
  Local Hint Resolve check_nclock_correct.

  Ltac solve_ndup :=
    unfold fresh_ins, idty in *; simpl in *; solve_NoDupMembers_app.
  (*   unfold idty in *; repeat rewrite map_app in *. *)
  (* Ltac ndup_l H := *)
  (*   ndup_simpl; *)
  (*   rewrite app_assoc in H; apply NoDupMembers_app_l in H; auto. *)
  (* Ltac ndup_r H := *)
  (*   ndup_simpl; *)
  (*   rewrite Permutation_swap in H; *)
  (*   apply NoDupMembers_app_r in H ; auto. *)

  Module NatOrder <: Orders.TotalLeBool.
    Definition t := nat.
    Definition leb := Nat.leb.
    Theorem leb_total :
      forall a1 a2, Nat.leb a1 a2 = true \/ Nat.leb a2 a1 = true.
    Proof.
      intros.
      destruct (Nat.leb a1 a2) eqn:He; auto.
      rewrite Nat.leb_gt, Nat.leb_le in *.
      lia.
    Qed.
  End NatOrder.

  Module SortNat := Mergesort.Sort(NatOrder).

  Scheme Equality for list.

  (** Check that `xs` is a permutation of [0;n[ *)
  Definition check_perm_seq xs n :=
    list_beq _ Nat.eqb (SortNat.sort xs) (seq 0 n).

  Lemma check_perm_seq_spec : forall xs n,
      check_perm_seq xs n = true ->
      Permutation xs (seq 0 n).
  Proof.
    unfold check_perm_seq.
    intros * Hce.
    apply internal_list_dec_bl in Hce. 2:apply Nat.eqb_eq.
    etransitivity. 2:rewrite <-Hce; eauto.
    apply SortNat.Permuted_sort.
  Qed.

  Fixpoint check_nodup_sorted xs :=
    match xs with
    | [] => true
    | x1::tl =>
      match tl with
      | [] => true
      | x2::_ => (negb (x1 =? x2)) && (check_nodup_sorted tl)
      end
    end.

  Fact check_nodup_sorted_NoDup : forall xs,
      StronglySorted le xs ->
      check_nodup_sorted xs = true ->
      NoDup xs.
  Proof.
    induction xs; intros * Hsort Hc; inv Hsort; simpl in *.
    - constructor; auto.
    - destruct xs; try solve [constructor; auto].
      eapply Bool.andb_true_iff in Hc as (Hc1&Hc2).
      constructor; auto.
      eapply Bool.negb_true_iff, Nat.eqb_neq in Hc1.
      intros contra.
      assert (Forall (lt a) (n::xs)) as Hlt.
      { inv H2. constructor; auto.
        - lia.
        - inv H1.
          eapply Forall_impl; [|eauto]; intros. lia. }
      eapply Forall_forall in Hlt; eauto. lia.
  Qed.

  Definition check_nodup_nat xs :=
    check_nodup_sorted (SortNat.sort xs).

  Lemma check_nodup_nat_NoDup : forall xs,
      check_nodup_nat xs = true ->
      NoDup xs.
  Proof.
    unfold check_nodup_nat.
    intros * Hc.
    apply check_nodup_sorted_NoDup in Hc; eauto.
    - now rewrite <-SortNat.Permuted_sort in Hc.
    - apply Sorted_StronglySorted. intros ?????. eapply Nat.le_trans; eauto.
      eapply Sorted_impl, SortNat.LocallySorted_sort.
      intros ?? Hle; simpl in *. inv Hle.
      apply Nat.leb_le; auto.
  Qed.

  Section ValidateExpression.
    Context {PSyn : block -> Prop}.
    Context {prefs : PS.t}.

    Variable G : @global PSyn prefs.
    Variable eenv : Env.t nat.
    Variable venv : Env.t type.

    Hypothesis Henums : incl (Env.elements eenv) G.(enums).

    Open Scope option_monad_scope.

    Definition check_paired_types2 (t1 : type) (tc : ann) : bool :=
      let '(t, c) := tc in
      (t1 ==b t) && (check_nclock eenv venv c).

    Definition check_paired_types3 (t1 t2 : type) (tc : ann) : bool :=
      let '(t, c) := tc in
      (t1 ==b t) && (t2 ==b t) && (check_nclock eenv venv c).

    Definition check_reset (tr : list (list type)) : bool :=
      forallb (fun tys => match tys with [ty] => ty ==b bool_velus_type | _ => false end) tr.

    Definition check_var (x : ident) (ty : type) : bool :=
      match Env.find x venv with
      | None => false
      | Some xt => ty ==b xt
      end.

    Definition check_enum ty : bool :=
      match ty with
      | Tenum (x, n) =>
        match Env.find x eenv with
        | None => false
        | Some n' => (n ==b n') && (0 <? n)
        end
      | _ => true
      end.

    Fixpoint check_exp (e : exp) : option (list type) :=
      match e with
      | Econst c => Some ([Tprimitive (ctype_cconst c)])

      | Eenum k (Tenum (xt, n)) =>
        if check_enum (Tenum (xt, n)) && (k <? n) then Some [Tenum (xt, n)] else None

      | Evar x (xt, nck) =>
        if check_var x xt && check_nclock eenv venv nck then Some [xt] else None

      | Eunop op e (xt, nck) =>
        do te <- assert_singleton (check_exp e);
        do t <- type_unop op te;
        if (xt ==b t) && check_enum t && check_nclock eenv venv nck then Some [xt] else None

      | Ebinop op e1 e2 (xt, nck) =>
        do te1 <- assert_singleton (check_exp e1);
        do te2 <- assert_singleton (check_exp e2);
        do t <- type_binop op te1 te2;
        if (xt ==b t) && check_enum t && check_nclock eenv venv nck then Some [xt] else None

      | Efby e0s es anns =>
        do t0s <- oconcat (map check_exp e0s);
        do ts <- oconcat (map check_exp es);
        if forall3b check_paired_types3 t0s ts anns
        then Some (map fst anns) else None

      | Earrow e0s es anns =>
        do t0s <- oconcat (map check_exp e0s);
        do ts <- oconcat (map check_exp es);
        if forall3b check_paired_types3 t0s ts anns
        then Some (map fst anns) else None

      | Ewhen es x k (tys, nck) =>
        do ts <- oconcat (map check_exp es);
        match Env.find x venv with
        | Some (Tenum (xt, n)) =>
          if check_enum (Tenum (xt, n)) && (k <? n) && (forall2b equiv_decb ts tys) && (check_nclock eenv venv nck)
          then Some tys else None
        | _ => None
        end

      | Emerge (x, Tenum (xt, n)) es (tys, nck) =>
        do tss <- omap (fun es => oconcat (map check_exp (snd es))) es;
        if check_var x (Tenum (xt, n)) && check_enum (Tenum (xt, n))
           && (check_perm_seq (map fst es) n) && (length es <>b 0)
           && (forallb (fun ts => forall2b equiv_decb ts tys) tss)
           && (check_nclock eenv venv nck)
        then Some tys else None

      | Ecase e brs None (tys, nck) =>
        do tss <- omap (fun es => oconcat (map check_exp (snd es))) brs;
        (* do tds <- oconcat (map check_exp d); *)
        do xt <- assert_singleton (check_exp e);
        match xt with
        | Tenum (xt, n) =>
          if check_enum (Tenum (xt, n))
             && (check_perm_seq (map fst brs) n) && (length brs <>b 0)
             && (forallb (fun ts => (forall2b equiv_decb ts tys)) tss)
             && (check_nclock eenv venv nck)
          then Some tys else None
        | _ => None
        end

      | Ecase e brs (Some d) (tys, nck) =>
        do tss <- omap (fun es => oconcat (map check_exp (snd es))) brs;
        do tds <- oconcat (map check_exp d);
        do xt <- assert_singleton (check_exp e);
        match xt with
        | Tenum (xt, n) =>
          if check_enum (Tenum (xt, n))
             && (check_nodup_nat (map fst brs)) && (forallb (fun i => i <? n) (map fst brs)) && (length brs <>b 0)
             && (forallb (fun ts => (forall2b equiv_decb ts tys)) (tds::tss))
             && (check_nclock eenv venv nck)
          then Some tys else None
        | _ => None
        end

      | Eapp f es er anns =>
        do n <- find_node f G;
        do ts <- oconcat (map check_exp es);
        do tr <- omap check_exp er;
        if (forall2b (fun et '(_, (t, _, _)) => et ==b t) ts n.(n_in))
             && (forall2b (fun '(ot, oc) '(_, (t, _, _)) =>
                             check_nclock eenv (Env.adds' (idty (fresh_ins es++anon_streams anns)) venv) oc
                             && (ot ==b t)) anns n.(n_out))
             && check_reset tr
        then Some (map fst anns)
        else None

      | _ => None
      end.

    Definition check_rhs (e : exp) : option (list type) :=
      match e with
      | Eapp f es er anns =>
        do n <- find_node f G;
        do ts <- oconcat (map check_exp es);
        do tr <- omap check_exp er;
        if (forall2b (fun et '(_, (t, _, _)) => et ==b t) ts n.(n_in))
             && (forall2b (fun '(ot, oc) '(_, (t, _, _)) =>
                             check_nclock eenv (Env.adds' (idty (fresh_ins es)) venv) oc
                             && (ot ==b t)) anns n.(n_out))
             && check_reset tr
        then Some (map fst anns)
        else None
      | e => check_exp e
      end.

    Definition check_equation (eq : equation) : bool :=
      let '(xs, es) := eq in
      match oconcat (map check_rhs es) with
      | None => false
      | Some tys => forall2b check_var xs tys
      end.

    Lemma check_var_correct:
      forall x ty,
        check_var x ty = true <-> In (x, ty) (Env.elements venv).
    Proof.
      unfold check_var. split; intros HH.
      - cases_eqn Heq; simpl.
        rewrite equiv_decb_equiv in HH. inv HH.
        take (Env.find _ _ = Some _) and apply Env.elements_correct in it; eauto.
      - apply Env.elements_complete in HH as ->.
        apply equiv_decb_refl.
    Qed.
    Local Hint Resolve check_var_correct.

    Lemma check_enum_correct':
      forall tx n,
        check_enum (Tenum (tx, n)) = true ->
        In (tx, n) G.(enums) /\ 0 < n.
    Proof.
      unfold check_enum. intros * HH.
      cases_eqn Heq; simpl.
      apply Bool.andb_true_iff in HH as (H1&H2).
      rewrite equiv_decb_equiv in H1. inv H1.
      take (Env.find _ _ = Some _) and apply Env.elements_correct in it; eauto.
      apply Nat.ltb_lt in H2. auto.
    Qed.
    Local Hint Resolve check_enum_correct'.

    Lemma check_enum_correct:
      forall ty,
        check_enum ty = true ->
        wt_enum G ty.
    Proof.
      unfold check_enum. intros * HH.
      cases_eqn Heq; simpl; auto.
      apply Bool.andb_true_iff in HH as (H1&H2).
      rewrite equiv_decb_equiv in H1. inv H1.
      take (Env.find _ _ = Some _) and apply Env.elements_correct in it; eauto.
      apply Nat.ltb_lt in H2. auto.
    Qed.
    Local Hint Resolve check_enum_correct.

    Lemma check_paired_types2_correct:
      forall tys1 anns,
        forall2b check_paired_types2 tys1 anns = true ->
        tys1 = map fst anns
        /\ Forall (wt_nclock G.(enums) (Env.elements venv)) (map snd anns).
    Proof.
      setoid_rewrite forall2b_Forall2.
      induction 1 as [|ty1 (ty, nck) tys1 anns IH1 IH3];
        subst; simpl; eauto.
      simpl in IH1.
      repeat rewrite Bool.andb_true_iff in IH1.
      setoid_rewrite equiv_decb_equiv in IH1.
      destruct IH1 as (-> & IH1).
      apply check_nclock_correct in IH1. rewrite Henums in IH1.
      destruct IHIH3; split; try f_equal; auto.
    Qed.

    Lemma check_paired_types3_correct:
      forall tys1 tys2 anns,
        forall3b check_paired_types3 tys1 tys2 anns = true ->
        tys1 = map fst anns
        /\ tys2 = map fst anns
        /\ Forall (wt_nclock G.(enums) (Env.elements venv)) (map snd anns).
    Proof.
      setoid_rewrite forall3b_Forall3.
      induction 1 as [|ty1 ty2 (ty, nck) tys1 tys2 anns IH1 IH2 (? & ? & IH3)];
        subst; simpl; eauto.
      simpl in IH1.
      repeat rewrite Bool.andb_true_iff in IH1.
      setoid_rewrite equiv_decb_equiv in IH1.
      destruct IH1 as ((-> & ->) & IH1).
      apply check_nclock_correct in IH1. rewrite Henums in IH1. auto.
    Qed.

    Lemma oconcat_map_check_exp':
      forall {f} es tys,
        (forall e tys,
            In e es ->
            NoDupMembers (Env.elements venv++idty (fresh_in e)) ->
            f e = Some tys ->
            wt_exp G (Env.elements venv) e /\ typeof e = tys) ->
        NoDupMembers (Env.elements venv++idty (fresh_ins es)) ->
        oconcat (map f es) = Some tys ->
        Forall (wt_exp G (Env.elements venv)) es
        /\ typesof es = tys.
    Proof.
      induction es as [|e es IH]; intros tys WTf ND CE. now inv CE; auto.
      simpl in CE. destruct (f e) eqn:Ce; [|now omonadInv CE].
      destruct (oconcat (map f es)) as [tes|]; [|now omonadInv CE].
      omonadInv CE. simpl.
      apply WTf in Ce as (Ce1 & ->); auto with datatypes.
      destruct (IH tes) as (? & ->); auto.
      intros * Ies ND' Fe. apply WTf in Fe; auto with datatypes.
      + unfold fresh_ins, idty in *; simpl in *. rewrite map_app in *.
        rewrite Permutation_swap in ND. apply NoDupMembers_app_r in ND; auto.
      + unfold fresh_ins, idty in *; simpl in *. rewrite map_app in *.
        rewrite app_assoc in ND. apply NoDupMembers_app_l in ND; auto.
    Qed.

    Lemma omap_concat_map_check_exp':
      forall {f} (ess : list (enumtag * _)) tys,
        (forall es e tys,
            In es ess ->
            In e (snd es) ->
            NoDupMembers (Env.elements venv++idty (fresh_in e)) ->
            f e = Some tys ->
            wt_exp G (Env.elements venv) e /\ typeof e = tys) ->
        NoDupMembers (Env.elements venv++idty (flat_map (fun es => fresh_ins (snd es)) ess)) ->
        omap (fun es => oconcat (map f (snd es))) ess = Some tys ->
        Forall (fun es => Forall (wt_exp G (Env.elements venv)) (snd es)) ess
        /\ Forall2 (fun es tys => typesof (snd es) = tys) ess tys.
    Proof with try solve_ndup.
      induction ess as [|es ess IH]; intros tys WTf ND CE. now inv CE; auto.
      simpl in CE. destruct (oconcat (map f (snd es))) eqn:Ce; [|now omonadInv CE].
      eapply oconcat_map_check_exp' in Ce as (?&?); eauto with datatypes...
      destruct (omap _ _) as [tes|]; [|now omonadInv CE]...
      omonadInv CE. simpl.
      specialize (IH tes) as (? & ?); eauto using in_cons...
    Qed.

    (* Lemma omap_concat_map_check_exp'': *)
    (*   forall {f} ess dty tys, *)
    (*     (forall es e tys, *)
    (*         In (Some es) ess -> *)
    (*         In e es -> *)
    (*         NoDupMembers (Env.elements venv++idty (fresh_in e)) -> *)
    (*         f e = Some tys -> *)
    (*         wt_exp G (Env.elements venv) e /\ typeof e = tys) -> *)
    (*     NoDupMembers (Env.elements venv++idty (flat_map (or_default_with [] fresh_ins) ess)) -> *)
    (*     omap (or_default_with (Some dty) (fun es => oconcat (map f es))) ess = Some tys -> *)
    (*     Forall (LiftO True (Forall (wt_exp G (Env.elements venv)))) ess *)
    (*     /\ Forall2 (fun es tys => LiftO True (fun es => typesof es = tys) es) ess tys. *)
    (* Proof with try solve_ndup. *)
    (*   induction ess as [|es ess IH]; intros * WTf ND CE. now inv CE; auto. *)
    (*   simpl in CE. *)
    (*   destruct es; simpl in *. *)
    (*   - destruct (oconcat (map _ l)) eqn:Ce; [|now omonadInv CE]. *)
    (*     destruct (omap _ _) as [tes|] eqn:CE''; [|now omonadInv CE]. *)
    (*     omonadInv CE. simpl. *)
    (*     eapply oconcat_map_check_exp' in Ce as (?&?); eauto with datatypes... *)
    (*     specialize (IH dty tes) as (? & ?); eauto using in_cons... *)
    (*   - destruct (omap _ _) as [tes|] eqn:CE'; [|now omonadInv CE]. *)
    (*     omonadInv CE. simpl. *)
    (*     specialize (IH dty tes) as (? & ?); eauto using in_cons. *)
    (*     split; constructor; simpl; auto. *)
    (* Qed. *)

    Lemma check_reset_correct :
      forall tys,
        check_reset tys = true ->
        Forall (fun ty => ty = [bool_velus_type]) tys.
    Proof.
      intros * Che.
      eapply forallb_Forall in Che.
      eapply Forall_impl; [|eauto]. intros ? Eq; simpl in Eq.
      destruct a as [|? [|? ?]]; try congruence.
      rewrite equiv_decb_equiv in Eq. inv Eq.
      reflexivity.
    Qed.

    Lemma omap_check_exp':
      forall {f} es tys,
        (forall e tys,
            In e es ->
            NoDupMembers (Env.elements venv++idty (fresh_in e)) ->
            f e = Some tys ->
            wt_exp G (Env.elements venv) e /\ typeof e = tys) ->
        NoDupMembers (Env.elements venv++idty (fresh_ins es)) ->
        omap f es = Some tys ->
        Forall (wt_exp G (Env.elements venv)) es
        /\ Forall2 (fun e ty => typeof e = ty) es tys.
    Proof with try solve_ndup.
      induction es as [|e es IH]; intros tys WTf ND CE. now inv CE; auto.
      simpl in CE. destruct (f e) eqn:Ce; [|now omonadInv CE].
      destruct (omap f es) as [tes|]; [|now omonadInv CE].
      omonadInv CE. simpl.
      apply WTf in Ce as (Ce1 & ?); auto with datatypes...
      destruct (IH tes) as (? & ?); auto with datatypes...
    Qed.

    Import Permutation.
    Local Hint Constructors wt_exp wt_block.
    Lemma check_exp_correct:
      forall e tys,
        NoDupMembers (Env.elements venv++(idty (fresh_in e))) ->
        check_exp e = Some tys ->
        wt_exp G (Env.elements venv) e
        /\ typeof e = tys.
    Proof with eauto.
      induction e using exp_ind2; simpl; intros tys ND CE. 10:destruct d; simpl in *.
      1-12:repeat progress
               match goal with
               | a:ann |- _ => destruct a
               | a:lann |- _ => destruct a
               | p:type * clock |- _ => destruct p
               | x:ident * type |- _ => destruct x
               | H:obind _ _ = Some _ |- _ => omonadInv H
               | H:obind2 _ _ = Some _ |- _ => omonadInv H
               | H:obind ?v _ = Some _ |- _ =>
                 let OE:=fresh "OE0" in destruct v eqn:OE; [simpl in H|now omonadInv H]
               | H: _ && _ = true |- _ => apply Bool.andb_true_iff in H as (? & ?)
               | H: ((_ ==b _) = true) |- _ => rewrite equiv_decb_equiv in H; inv H
               | H: check_nclock _ _ _ = true |- _ => apply check_nclock_correct in H; rewrite Henums in H
               | H: Env.find _ _ = Some _ |- _ => apply Env.elements_correct in H
               | H:(obind2 (Env.find ?x ?env) _) = Some _ |- _ =>
                 let EF := fresh "EF0" in
                 destruct (Env.find x env) eqn:EF
               | H:(if ?c then Some _ else None) = Some _ |- _ =>
                 let C := fresh "C0" in
                 destruct c eqn:C
               | H:match (Env.find ?env ?x) with
                   | Some _ => _ | None => None
                   end = Some _ |- _ => destruct (Env.find env x) eqn:Hfind; try congruence
               | H:match ?ty with
                   | Tprimitive _ => None | Tenum _ => _
                   end = Some _ |- _ => destruct ty as [|(?&?)]; try congruence
               | H:None = Some _ |- _ => discriminate
               | H:Some _ = Some _ |- _ => inv H
               | H:assert_singleton _ = Some _ |- _ => apply assert_singleton_spec in H
               | H:check_var _ _ = true |- _ => apply check_var_correct in H
               | H:check_enum _ = true |- _ => apply check_enum_correct in H
               | H:(_ <? _) = true |- _ => rewrite Nat.ltb_lt in H
               | H:forall2b check_paired_types2 ?tys1 ?anns = true |- _ =>
                 apply check_paired_types2_correct in H as (? & ?)
               | H:forall3b check_paired_types3 ?tys1 ?tys2 ?anns = true |- _ =>
                 apply check_paired_types3_correct in H as (? & ? & ?)
               | H:forall2b equiv_decb ?xs ?ys = true |- _ =>
                 apply forall2b_Forall2_equiv_decb in H
               | H:forallb (fun ts => forall2b equiv_decb ts _) _ = true |- _ =>
                 apply forallb_forall2b_equiv_decb in H
               | H:Forall2 eq _ _ |- _ => apply Forall2_eq in H
               | H:forall2b _ _ _ = true |- _ => apply forall2b_Forall2 in H
               end...

      - (* Eenum *)
        eapply check_enum_correct' in H as (?&?)...
      - (* Eunop *)
        apply IHe in OE0 as (? & ?)...
      - (* Ebinop *)
        apply IHe1 in OE0 as (? & ?); apply IHe2 in OE1 as (? & ?)... 1-3:solve_ndup.
      - (* Efby *)
        take (Forall _ e0s) and rewrite Forall_forall in it.
        take (Forall _ es) and rewrite Forall_forall in it.
        apply oconcat_map_check_exp' in OE0 as (? & ?)...
        apply oconcat_map_check_exp' in OE1 as (? & ?)...
        2,3:solve_ndup.
        repeat constructor; eauto. 1,2:congruence.
      - (* Earrow *)
        take (Forall _ e0s) and rewrite Forall_forall in it.
        take (Forall _ es) and rewrite Forall_forall in it.
        apply oconcat_map_check_exp' in OE0 as (? & ?)...
        apply oconcat_map_check_exp' in OE1 as (? & ?)...
        2,3:solve_ndup.
        repeat constructor; eauto. 1,2:congruence.
      - (* Ewhen *)
        subst. take (Forall _ es) and rewrite Forall_forall in it.
        take (oconcat (map check_exp _) = Some _) and
             apply oconcat_map_check_exp' in it as (? & ?)...
        eapply check_enum_correct' in H0 as (?&?)...
      - (* Emerge *)
        take (Forall _ es) and (repeat setoid_rewrite Forall_forall in it).
        take (omap _ _ = Some _) and
             apply omap_concat_map_check_exp' in it as (Hwt & Hty); eauto.
        econstructor; eauto. econstructor; eauto.
        + eapply check_enum_correct' in H5 as (?&?)...
        + eapply check_perm_seq_spec in H4...
        + contradict H3; subst; simpl.
          apply Bool.not_true_iff_false, nequiv_decb_false, equiv_decb_equiv. constructor.
        + eapply Forall2_ignore2 in Hty.
          eapply Forall_impl; [|eapply Hty]; intros (?&?) (?&Hin&Hty').
          eapply Forall_forall in H2; eauto. rewrite Forall2_eq in H2; subst; auto.
      - (* Ecase *)
        take (check_exp _ = Some _) and apply IHe in it as (? & ?). 2:solve_ndup.
        take (Forall _ es) and (repeat setoid_rewrite Forall_forall in it).
        take (omap _ _ = Some _) and
             apply omap_concat_map_check_exp' in it as (Hwt & Hty); eauto. 2:solve_ndup.
        take (Forall _ l) and (repeat setoid_rewrite Forall_forall in it).
        eapply oconcat_map_check_exp' in OE1 as (? & ?)... 2:solve_ndup.
        do 2 econstructor; eauto.
        + apply check_enum_correct' in H1 as (?&?)...
        + intros ? Hin.
          eapply forallb_Forall, Forall_forall in H6; eauto. eapply Nat.ltb_lt in H6.
          eapply in_seq. split; simpl; lia.
        + eapply check_nodup_nat_NoDup, fst_NoDupMembers in H7...
        + contradict H5; subst; simpl.
          apply Bool.not_true_iff_false, nequiv_decb_false, equiv_decb_equiv. constructor.
        + eapply Forall2_ignore2 in Hty.
          eapply Forall_impl; [|eapply Hty]; intros (?&?) (?&Hin&Hty').
          eapply Forall_forall in H4; eauto. rewrite Forall2_eq in H4; subst; auto.
        + congruence.
      - (* Ecase *)
        take (check_exp _ = Some _) and apply IHe in it as (? & ?). 2:solve_ndup.
        take (Forall _ es) and (repeat setoid_rewrite Forall_forall in it).
        take (omap _ _ = Some _) and
             apply omap_concat_map_check_exp' in it as (Hwt & Hty); eauto. 2:solve_ndup.
        do 2 econstructor; eauto.
        + apply check_enum_correct' in H1 as (?&?)...
        + eapply check_perm_seq_spec in H5...
        + contradict H4; subst; simpl.
          apply Bool.not_true_iff_false, nequiv_decb_false, equiv_decb_equiv. constructor.
        + eapply Forall2_ignore2 in Hty.
          eapply Forall_impl; [|eapply Hty]; intros (?&?) (?&Hin&Hty').
          eapply Forall_forall in H3; eauto. rewrite Forall2_eq in H3; subst; auto.
      - (* Eapp *)
        take (Forall _ es) and rewrite Forall_forall in it.
        take (Forall _ er) and rewrite Forall_forall in it.
        take (oconcat (map check_exp _) = Some _) and
             apply oconcat_map_check_exp' in it as (? & ?); auto. 2:solve_ndup.
        take (omap check_exp _ = Some _) and
             apply omap_check_exp' in it as (? & ?); auto. 2:solve_ndup.
        split; auto. subst.
        assert (Forall2 (fun et '(_, (t, _, _)) => et = t) (typesof es) n.(n_in)).
        { take (Forall2 _ (typesof es) n.(n_in))
               and apply Forall2_impl_In with (2:=it).
          intros ? (? & ((?&?)&?)) ? ? EQ.
          now rewrite equiv_decb_equiv in EQ. }
        assert (Forall2 (fun ann '(_, (t, _, _)) => fst ann = t) a n.(n_out)).
        { take (Forall2 _ _ n.(n_out)) and apply Forall2_impl_In with (2:=it).
          intros (? & ?) (? & ((?&?)&?)) ? ? EQ.
          apply Bool.andb_true_iff in EQ as (EQ1 & EQ2).
          now rewrite equiv_decb_equiv in EQ2. }
        assert (Forall (fun ann => wt_nclock G.(enums) ((Env.elements venv)++idty (fresh_ins es++anon_streams a)) (snd ann)) a).
        { repeat take (Forall2 _ _ n.(n_out)) and apply Forall2_ignore2 in it.
          apply Forall_impl_In with (2:=it).
          intros (? & ?) ? ((? & ((?&?)&?)) & (? & EQ)); simpl.
          apply Bool.andb_true_iff in EQ as (EQ1 & EQ2).
          apply check_nclock_correct in EQ1. rewrite Henums, Env.elements_adds in EQ1; auto.
          solve_ndup.
        }
        econstructor; eauto; simpl in *;
          clear it; cases_eqn E; subst.
        eapply check_reset_correct in H2.
        eapply Forall2_ignore1' in H2. 2:symmetry; eapply Forall2_length; eauto.
        eapply Forall2_Forall2, Forall2_ignore2 in H5; eauto.
        eapply Forall_impl; [|eauto]. intros ? (?&?&?&?); congruence.
    Qed.

    Corollary oconcat_map_check_exp:
      forall es tys,
        NoDupMembers (Env.elements venv++idty (fresh_ins es)) ->
        oconcat (map check_exp es) = Some tys ->
        Forall (wt_exp G (Env.elements venv)) es
        /\ typesof es = tys.
    Proof.
      intros.
      eapply oconcat_map_check_exp'; eauto.
      intros. eapply check_exp_correct; eauto.
    Qed.

    Corollary omap_check_exp:
      forall es tys,
        NoDupMembers (Env.elements venv++idty (fresh_ins es)) ->
        omap check_exp es = Some tys ->
        Forall (wt_exp G (Env.elements venv)) es
        /\ Forall2 (fun e ty => typeof e = ty) es tys.
    Proof.
      intros.
      eapply omap_check_exp'; eauto.
      intros. eapply check_exp_correct; eauto.
    Qed.

    Lemma check_rhs_correct:
      forall e tys,
        NoDupMembers (Env.elements venv++(idty (anon_in e))) ->
        check_rhs e = Some tys ->
        wt_exp G (Env.elements venv) e
        /\ typeof e = tys.
    Proof with eauto.
      intros e tys ND CR.
      destruct e; try (now apply check_exp_correct).
      simpl in CR.

      repeat progress
               match goal with
               | H:obind ?v _ = Some _ |- _ =>
                 let OE:=fresh "OE0" in destruct v eqn:OE; [simpl in H|now omonadInv H]
               | H: _ && _ = true |- _ => apply Bool.andb_true_iff in H as (? & ?)
               | H: ((_ ==b _) = true) |- _ => rewrite equiv_decb_equiv in H; inv H
               | H: check_nclock _ = true |- _ => apply check_nclock_correct in H
               | H: Env.find _ _ = Some _ |- _ => apply Env.elements_correct in H
               | H:(if ?c then Some _ else None) = Some _ |- _ =>
                 let C := fresh "C0" in
                 destruct c eqn:C
               | H:None = Some _ |- _ => discriminate
               | H:Some _ = Some _ |- _ => inv H
               | H:forall2b _ _ _ = true |- _ => apply forall2b_Forall2 in H
               end...
      split...

      simpl in ND.
      take (oconcat (map check_exp _) = Some _) and
           apply oconcat_map_check_exp in it as (? & ?); auto. 2:solve_ndup.
      take (omap check_exp _ = Some _) and
             apply omap_check_exp in it as (? & ?); auto. 2:solve_ndup.
      subst.
      assert (Forall2 (fun et '(_, (t, _, _)) => et = t) (typesof l) n.(n_in)).
        { take (Forall2 _ (typesof l) n.(n_in))
               and apply Forall2_impl_In with (2:=it).
          intros ? (? & ((?&?)&?)) ? ? EQ.
          now rewrite equiv_decb_equiv in EQ. }
        assert (Forall2 (fun ann '(_, (t, _, _)) => fst ann = t) l1 n.(n_out)).
        { take (Forall2 _ _ n.(n_out)) and apply Forall2_impl_In with (2:=it).
          intros (? & ?) (? & ((?&?)&?)) ? ? EQ.
          apply Bool.andb_true_iff in EQ as (EQ1 & EQ2).
          now rewrite equiv_decb_equiv in EQ2. }
        assert (Forall (fun a => wt_nclock G.(enums) (Env.elements venv ++ idty (fresh_ins l++anon_streams l1)) (snd a)) l1).
        { repeat take (Forall2 _ _ n.(n_out)) and apply Forall2_ignore2 in it.
          apply Forall_impl_In with (2:=it).
          intros (? & ?) ? ((? & ((?&?)&?)) & (? & EQ)); simpl.
          apply Bool.andb_true_iff in EQ as (EQ1 & EQ2).
          unfold idty in *; rewrite map_app in *.
          apply check_nclock_correct in EQ1. rewrite Henums, Env.elements_adds in EQ1; auto.
          + eapply wt_nclock_incl; [| eauto]. apply incl_appr'.
            eapply incl_appl. reflexivity.
          + rewrite app_assoc in ND.
            apply NoDupMembers_app_l in ND. assumption. }
        simpl in H1; cases_eqn E; econstructor...
        eapply check_reset_correct in H0.
        eapply Forall2_ignore1' in H0. 2:symmetry; eapply Forall2_length; eauto.
        eapply Forall2_Forall2, Forall2_ignore2 in H5; eauto.
        eapply Forall_impl; [|eauto]. intros ? (?&?&?&?); congruence.
    Qed.

    Corollary oconcat_map_check_rhs:
      forall es tys,
        NoDupMembers (Env.elements venv++idty (anon_ins es)) ->
        oconcat (map check_rhs es) = Some tys ->
        Forall (wt_exp G (Env.elements venv)) es
        /\ typesof es = tys.
    Proof.
      induction es as [|e es IH]; intros tys ND CE. now inv CE; auto.
      simpl in CE. destruct (check_rhs e) eqn:Ce; [|now omonadInv CE].
      destruct (oconcat (map check_rhs es)) as [tes|]; [|now omonadInv CE].
      omonadInv CE. simpl.
      apply check_rhs_correct in Ce as (Ce1 & ->); auto with datatypes.
      destruct (IH tes) as (? & ->); auto.
      + unfold anon_ins, idty in *; simpl in *. rewrite map_app in *.
        rewrite Permutation_swap in ND. apply NoDupMembers_app_r in ND; auto.
      + unfold anon_ins, idty in *; simpl in *. rewrite map_app in *.
        rewrite app_assoc in ND. apply NoDupMembers_app_l in ND; auto.
    Qed.

    Lemma check_equation_correct:
      forall eq,
        NoDupMembers (Env.elements venv++(idty (anon_in_eq eq))) ->
        check_equation eq = true ->
        wt_equation G (Env.elements venv) eq.
    Proof.
      intros eq ND CE. destruct eq as (xs, es); simpl in CE.
      cases_eqn Heq.
      take (oconcat (map check_rhs _) = Some _)
           and apply oconcat_map_check_rhs in it as (? & ?).
      take (forall2b check_var _ _ = true)
           and apply forall2b_Forall2 in it.
      setoid_rewrite check_var_correct in it.
      subst; constructor; auto.
      unfold anon_in_eq in ND; auto.
    Qed.

  End ValidateExpression.

  Section ValidateBlock.
    Context {PSyn : block -> Prop}.
    Context {prefs : PS.t}.
    Variable (G : @global PSyn prefs).

    Variable (eenv : Env.t nat).
    Hypothesis Henums : incl (Env.elements eenv) G.(enums).

    Fixpoint check_block (venv : Env.t type) (d : block) : bool :=
      match d with
      | Beq eq => check_equation G eenv venv eq
      | Breset blocks er =>
        forallb (check_block venv) blocks &&
        match check_exp G eenv venv er with
        | Some [tyr] => tyr ==b bool_velus_type
        | _ => false
        end
      | Blocal locs blocks =>
        let env' := Env.union venv (Env.from_list (idty (idty locs))) in
        forallb (check_block env') blocks &&
        forallb (check_clock eenv env') (map (fun '(_, (_, ck, _)) => ck) locs) &&
        forallb (check_enum eenv) (map snd (idty (idty locs)))
      end.

    Hint Constructors wt_block.

    Import Permutation.

    Lemma check_block_correct : forall blk venv,
        NoDupMembers (Env.elements venv++idty (anon_in_block blk)) ->
        NoDupLocals (map fst (Env.elements venv)++map fst (anon_in_block blk)) blk ->
        check_block venv blk = true ->
        wt_block G (Env.elements venv) blk.
    Proof.
      induction blk using block_ind2; intros * ND1 ND2 CD; inv ND2; simpl in *.
      - eapply check_equation_correct in CD; eauto.
      - eapply Bool.andb_true_iff in CD as (CDs&CE).
        eapply forallb_Forall in CDs.
        destruct check_exp eqn:CE'; try congruence.
        eapply check_exp_correct in CE' as (Wte&Tye); eauto. 2:solve_ndup.
        econstructor; eauto.
        + clear - H ND1 H2 CDs.
          eapply Forall_Forall in H; eauto. clear CDs.
          induction H as [|?? (?&?)]; simpl in *; inv H2; constructor; auto.
          * apply H0; eauto. solve_ndup.
            eapply NoDupLocals_incl; [|eauto]. solve_incl_app.
          * apply IHForall; eauto. solve_ndup.
            eapply Forall_impl; [|eapply H6]; intros.
            eapply NoDupLocals_incl; [|eauto]. solve_incl_app.
        + cases.
          rewrite equiv_decb_equiv in CE; inv CE.
          assumption.
      - repeat rewrite Bool.andb_true_iff in CD. destruct CD as ((CB&CC)&CE).
        apply forallb_Forall in CB. apply forallb_Forall in CC. apply forallb_Forall in CE.
        assert (NoDupMembers (idty (idty locs))) as Hnd1.
        { eapply NoDupMembers_idty, NoDupMembers_idty; eauto. }
        assert (forall x0, Env.In x0 venv -> ~ Env.In x0 (Env.from_list (idty (idty locs)))) as Hnd2.
        { intros ? Hin1 Hin2. eapply Env.In_Members in Hin1.
          eapply Env.In_from_list in Hin2. rewrite 2 InMembers_idty in Hin2.
          eapply H5; eauto. eapply in_app_iff, or_introl. eapply fst_InMembers; eauto. }
        constructor.
        + eapply Forall_Forall in H; [|eapply CB]. clear CB.
          induction H as [|?? (?&?)]; inv H2; simpl in *; constructor; auto.
          * eapply H0 in H. eapply wt_block_incl; [|eauto].
            1-3:rewrite Env.elements_union; try rewrite Env.elements_from_list; auto.
            -- rewrite idty_app in ND1.
              rewrite <-app_assoc, Permutation_swap. apply NoDupMembers_app; auto. solve_NoDupMembers_app.
              intros ? Hinm. rewrite 2 InMembers_idty in Hinm.
              apply H5 in Hinm. contradict Hinm.
              rewrite fst_InMembers, map_app, map_fst_idty in Hinm. rewrite map_app.
              repeat rewrite in_app_iff in *. destruct Hinm; auto.
            -- eapply NoDupLocals_incl; [|eauto]. repeat rewrite map_app. repeat rewrite map_fst_idty.
               repeat rewrite <-app_assoc. rewrite (Permutation_app_comm (map fst locs)). solve_incl_app.
          * apply IHForall; eauto.
            -- rewrite idty_app in ND1. solve_NoDupMembers_app.
            -- eapply Forall_impl; [|eapply H8]; intros.
               eapply NoDupLocals_incl; [|eauto]. repeat rewrite map_app. repeat rewrite map_fst_idty.
               solve_incl_app.
            -- intros ? Hinm. eapply H5 in Hinm. contradict Hinm.
               rewrite map_app. repeat rewrite in_app_iff in *. destruct Hinm; auto.
        + rewrite Forall_map in CC. eapply Forall_impl; eauto; intros (?&(?&?)&?) Hc.
          eapply check_clock_correct in Hc.
          rewrite Env.elements_union in Hc; try rewrite Env.elements_from_list in Hc; eauto.
          rewrite Henums in Hc; auto.
        + eapply Forall_impl; [|eauto]; intros ? Henum.
          eapply check_enum_correct; eauto.
    Qed.
  End ValidateBlock.

  Section ValidateGlobal.
    Definition check_node {PSyn prefs} (G : @global PSyn prefs) eenv (n : @node PSyn prefs) :=
      let ins := idty (idty (n_in n)) in
      let insouts := idty (idty (n_in n ++ n_out n)) in
      forallb (check_clock eenv (Env.from_list ins)) (List.map (fun '(_, (_, ck, _)) => ck) (n_in n)) &&
      forallb (check_clock eenv (Env.from_list insouts)) (List.map (fun '(_, (_, ck, _)) => ck) (n_out n)) &&
      forallb (check_enum eenv) (map snd insouts) &&
      check_block G eenv (Env.from_list insouts) (n_block n).

    Definition check_global {PSyn prefs} (G : @global PSyn prefs) :=
      let eenv := Env.from_list G.(enums) in
      check_enum eenv (Tenum (bool_id, 2)) &&
      check_nodup (List.map n_name G.(nodes)) &&
      (fix aux nds := match nds with
                    | [] => true
                    | hd::tl => check_node (update G tl) eenv hd && aux tl
                    end) G.(nodes).

    Lemma check_node_correct {PSyn prefs} : forall (G: @global PSyn prefs) eenv n,
        incl (Env.elements eenv) G.(enums) ->
        check_node G eenv n = true ->
        wt_node G n.
    Proof.
      intros * Hincl Hcheck.
      specialize (n_nodup n) as (Hdndup1&_).
      unfold check_node in Hcheck.
      repeat rewrite Bool.andb_true_iff in Hcheck. destruct Hcheck as [[[Hc1 Hc2] Hc3] Hc4].
      rewrite forallb_Forall, Forall_map in Hc1, Hc2.
      rewrite forallb_Forall in Hc3.
      split; [|split; [|split]].
      1-2:(eapply Forall_impl; eauto;
           intros [_ [[_ ?] ?]] Hck;
           eapply check_clock_correct in Hck; rewrite Hincl in Hck;
           eapply wt_clock_incl; [|eauto]; eapply Env.elements_from_list_incl).
      - eapply Forall_impl; [|eauto].
        intros. eapply check_enum_correct; eauto.
      - eapply check_block_correct in Hc4; auto.
        2,3:rewrite Env.elements_from_list.
        3,5:rewrite 2 NoDupMembers_idty; apply fst_NoDupMembers, node_NoDup.
        + eapply wt_block_incl; [|eauto]. eapply Env.elements_from_list_incl.
        + rewrite <-idty_app, NoDupMembers_idty. apply n_nodup.
        + rewrite 2 map_fst_idty. apply n_nodup.
    Qed.

    Lemma check_global_correct {PSyn prefs} : forall (G: @global PSyn prefs),
        check_global G = true ->
        wt_global G.
    Proof.
      intros G Hcheck.
      unfold check_global in Hcheck.
      repeat rewrite Bool.andb_true_iff in Hcheck. destruct Hcheck as [[Hbool Hndup] Hcheck].
      eapply check_enum_correct in Hbool; eauto using Env.elements_from_list_incl. destruct Hbool as (Hbool&_).
      apply check_nodup_correct in Hndup.
      unfold wt_global, wt_program, units; simpl. split; auto.
      induction (nodes G); constructor; inv Hndup.
      1-3:simpl in Hcheck; apply Bool.andb_true_iff in Hcheck as [Hc1 Hc2]; auto.
      split.
      - apply check_node_correct in Hc1; auto using Env.elements_from_list_incl.
      - apply Forall_forall. intros ? Hin contra.
        apply H1. rewrite in_map_iff. exists x; split; auto.
    Qed.
  End ValidateGlobal.

  Section interface_eq.
    Context {PSyn1 PSyn2 : block -> Prop}.
    Context {prefs1 prefs2 : PS.t}.
    Variable G1 : @global PSyn1 prefs1.
    Variable G2 : @global PSyn2 prefs2.

    Hypothesis Heq : global_iface_eq G1 G2.

    Fact iface_eq_wt_clock : forall vars ck,
        wt_clock G1.(enums) vars ck ->
        wt_clock G2.(enums) vars ck.
    Proof.
      intros * Hwt.
      destruct Heq as (?&?). congruence.
    Qed.

    Corollary iface_eq_wt_nclock : forall vars nck,
        wt_nclock G1.(enums) vars nck ->
        wt_nclock G2.(enums) vars nck.
    Proof.
      intros * Hwt. inv Hwt.
      constructor. eapply iface_eq_wt_clock; eauto.
    Qed.

    Lemma iface_eq_wt_enum : forall ty,
        wt_enum G1 ty ->
        wt_enum G2 ty.
    Proof.
      destruct Heq as (Henums&_).
      intros [|] Henum; simpl in *; auto.
      congruence.
    Qed.
    Hint Resolve iface_eq_wt_enum.

    Hint Constructors wt_exp.
    Fact iface_eq_wt_exp : forall vars e,
        wt_exp G1 vars e ->
        wt_exp G2 vars e.
    Proof with eauto.
      induction e using exp_ind2; intros Hwt; inv Hwt...
      1-10:econstructor; try (destruct Heq as (Henums&_); erewrite <-Henums)...
      1-12:rewrite Forall_forall in *...
      - intros ? Hin. specialize (H7 _ Hin). specialize (H _ Hin).
        rewrite Forall_forall in *...
      - intros ? Hin. specialize (H10 _ Hin). specialize (H _ Hin); simpl in H.
        rewrite Forall_forall in *...
      - intros ? Hin. specialize (H11 _ Hin). specialize (H _ Hin); simpl in H.
        rewrite Forall_forall in *...
      - simpl in *. intros ? Hin. eapply Forall_forall in H0; eauto.
      - (* app *)
        assert (Forall (wt_exp G2 vars) es) as Hwt by (rewrite Forall_forall in *; eauto).
        assert (Forall (wt_exp G2 vars) er) as Hwt' by (rewrite Forall_forall in *; eauto).
        destruct Heq as (Hequiv&Heq'). specialize (Heq' f).
        remember (find_node f G2) as find.
        destruct Heq'.
        + congruence.
        + inv H7.
          destruct H1 as [? [? [? ?]]].
          apply wt_Eapp with (n0:=sy)...
          * congruence.
          * congruence.
          * eapply Forall_forall...
          * eapply Forall_forall...
            erewrite <-Hequiv...
    Qed.

    Fact iface_eq_wt_equation : forall vars equ,
        wt_equation G1 vars equ ->
        wt_equation G2 vars equ.
    Proof.
      intros vars [xs es] Hwt.
      simpl in *. destruct Hwt.
      split.
      + rewrite Forall_forall in *. intros x Hin.
        eapply iface_eq_wt_exp; eauto.
      + assumption.
    Qed.

    Fact iface_eq_wt_block : forall d vars,
        wt_block G1 vars d ->
        wt_block G2 vars d.
    Proof.
      induction d using block_ind2; intros * Hwt; inv Hwt.
      - constructor; auto using iface_eq_wt_equation.
      - constructor; auto using iface_eq_wt_exp.
        rewrite Forall_forall in *; eauto.
      - constructor.
        1,3:rewrite Forall_forall in *; eauto.
        eapply Forall_impl; [|eauto]; intros (?&(?&?)&?) Hwt.
        apply iface_eq_wt_clock; auto.
    Qed.

  End interface_eq.

  (** *** wt implies wl *)

  Hint Constructors wl_exp wl_block.

  Fact wt_exp_wl_exp {PSyn prefs} : forall (G: @global PSyn prefs) vars e,
      wt_exp G vars e ->
      wl_exp G e.
  Proof with eauto.
    induction e using exp_ind2; intro Hwt; inv Hwt; simpl in *; auto.
    - (* unop *)
      constructor...
      rewrite <- length_typeof_numstreams. rewrite H3. reflexivity.
    - (* binop *)
      constructor...
      + rewrite <- length_typeof_numstreams. rewrite H5. reflexivity.
      + rewrite <- length_typeof_numstreams. rewrite H6. reflexivity.
    - (* fby *)
      constructor...
      + rewrite Forall_forall in *...
      + rewrite Forall_forall in *...
      + rewrite typesof_annots in *.
        erewrite <- map_length, H7, map_length...
      + rewrite typesof_annots in *.
        erewrite <- map_length, H6, map_length...
    - (* arrow *)
      constructor...
      + rewrite Forall_forall in *...
      + rewrite Forall_forall in *...
      + rewrite typesof_annots in *.
        erewrite <- map_length, H7, map_length...
      + rewrite typesof_annots in *.
        erewrite <- map_length, H6, map_length...
    - (* when *)
      constructor...
      + rewrite Forall_forall in *...
      + rewrite typesof_annots. rewrite map_length...
    - (* merge *)
      constructor...
      + rewrite Forall_forall in *...
        intros ? Hin. specialize (H _ Hin). specialize (H7 _ Hin).
        rewrite Forall_forall in *...
      + rewrite Forall_forall in *...
        intros. erewrite <- H8; eauto.
        rewrite typesof_annots, map_length...
    - (* case *)
      constructor...
      + rewrite <- length_typeof_numstreams, H6...
      + rewrite Forall_forall in *...
        intros ? Hin. specialize (H _ Hin); simpl in H. specialize (H10 _ Hin).
        rewrite Forall_forall in *...
      + rewrite Forall_forall in *...
        intros. erewrite <- H11; eauto.
        rewrite typesof_annots, map_length...
      + intros ? contra. inv contra.
      + intros ? contra. inv contra.
    - (* case (default) *)
      constructor...
      + rewrite <- length_typeof_numstreams, H6...
      + rewrite Forall_forall in *...
        intros ? Hin. specialize (H _ Hin); simpl in H. specialize (H11 _ Hin).
        rewrite Forall_forall in *...
      + rewrite Forall_forall in *...
        intros. erewrite <- H12; eauto.
        rewrite typesof_annots, map_length...
      + intros ? Heq; inv Heq.
        rewrite Forall_forall in *...
      + intros ? Heq; inv Heq.
        now rewrite length_typesof_annots.
    - (* app *)
      econstructor...
      + rewrite Forall_forall in *...
      + rewrite Forall_forall in *...
      + eapply Forall_impl; [|eapply H10]; intros ? Typ.
        rewrite <-length_typeof_numstreams, Typ...
      + apply Forall2_length in H8. rewrite typesof_annots, map_length in H8...
      + apply Forall2_length in H9...
  Qed.
  Hint Resolve wt_exp_wl_exp.

  Corollary Forall_wt_exp_wl_exp {PSyn prefs} : forall (G: @global PSyn prefs) vars es,
      Forall (wt_exp G vars) es ->
      Forall (wl_exp G) es.
  Proof. intros. rewrite Forall_forall in *; eauto. Qed.
  Hint Resolve Forall_wt_exp_wl_exp.

  Fact wt_equation_wl_equation {PSyn prefs} : forall (G: @global PSyn prefs) vars equ,
      wt_equation G vars equ ->
      wl_equation G equ.
  Proof with eauto.
    intros G vars [xs es] Hwt.
    inv Hwt. constructor.
    + rewrite Forall_forall in *...
    + apply Forall2_length in H0.
      rewrite typesof_annots, map_length in H0...
  Qed.
  Hint Resolve wt_equation_wl_equation.

  Fact wt_block_wl_block {PSyn prefs} : forall (G: @global PSyn prefs) d vars,
      wt_block G vars d ->
      wl_block G d.
  Proof.
    induction d using block_ind2; intros * Wt; inv Wt; eauto.
    - econstructor; eauto.
      + eapply Forall_Forall in H; eauto. clear H2.
        eapply Forall_impl; [|eauto]. intros ? (?&?); eauto.
      + now rewrite <-length_typeof_numstreams, H5.
    - econstructor; eauto.
      rewrite Forall_forall in *; eauto.
  Qed.
  Hint Resolve wt_block_wl_block.

  Fact wt_node_wl_node {PSyn prefs} : forall (G: @global PSyn prefs) n,
      wt_node G n ->
      wl_node G n.
  Proof with eauto.
    intros G n [_ [_ [_ Hwt]]].
    unfold wl_node...
  Qed.
  Hint Resolve wt_node_wl_node.

  Fact wt_global_wl_global {PSyn prefs} : forall (G: @global PSyn prefs),
      wt_global G ->
      wl_global G.
  Proof with eauto.
    intros G (_&Hwt).
    unfold wl_global, wt_program in *.
    induction Hwt; constructor...
    destruct H...
  Qed.
  Hint Resolve wt_global_wl_global.

  (** *** If an expression is well-typed, all the enums appearing inside are well-typed *)
  Section wt_enum.
    Context {PSyn : block -> Prop}.
    Context {prefs : PS.t}.
    Variable G : @global PSyn prefs.

    Hypothesis HwtG : wt_global G.

    Lemma wt_exp_wt_enum : forall vars e,
        Forall (wt_enum G) (map snd vars) ->
        wt_exp G vars e ->
        Forall (wt_enum G) (typeof e).
    Proof.
      induction e using exp_ind2; intros * Hvars Hwt; inv Hwt; simpl.
      - (* const *)
        repeat constructor.
      - (* enum *)
        repeat constructor; auto. lia.
      - (* var *)
        repeat constructor.
        rewrite Forall_map in Hvars.
        eapply Forall_forall in Hvars; eauto. auto.
      - (* unop *) constructor; auto.
      - (* binop *) constructor; auto.
      - (* fby *)
        rewrite <-H7. unfold typesof.
        rewrite flat_map_concat_map, <-Forall_concat, Forall_map.
        rewrite Forall_forall in H4, H. eapply Forall_forall; eauto.
      - (* arrow *)
        rewrite <-H7. unfold typesof.
        rewrite flat_map_concat_map, <-Forall_concat, Forall_map.
        rewrite Forall_forall in H4, H. eapply Forall_forall; eauto.
      - (* when *)
        unfold typesof.
        rewrite flat_map_concat_map, <-Forall_concat, Forall_map.
        rewrite Forall_forall in H7, H. eapply Forall_forall; eauto.
      - (* merge *)
        inv H; try solve [exfalso; eauto]. inv H7. inv H8.
        unfold typesof.
        rewrite flat_map_concat_map, <-Forall_concat, Forall_map.
        rewrite Forall_forall in H10, H0. eapply Forall_forall; eauto.
      - (* case *)
        inv H11; try congruence.
        unfold typesof.
        rewrite flat_map_concat_map, <-Forall_concat, Forall_map.
        inv H. inv H10. rewrite Forall_forall in *; intros. eapply H4; eauto.
        eapply Forall_forall; eauto.
      - (* case (default) *)
        simpl in *.
        unfold typesof.
        rewrite flat_map_concat_map, <-Forall_concat, Forall_map.
        eapply Forall_impl_In; [|eapply H0]; intros.
        eapply H2; eauto. rewrite Forall_forall in *; eauto.
      - (* app *)
        eapply wt_find_node in H7 as (?&Hwtn&Heq); eauto.
        destruct Hwtn as (_&_&Henums&_).
        unfold idty in Henums. repeat rewrite Forall_map in Henums.
        repeat rewrite Forall_app in Henums. destruct Henums as (_&Henums).
        rewrite Forall_map.
        eapply Forall2_ignore2 in H9.
        eapply Forall_impl; [|eapply H9]. intros (?&?) ((?&(?&?)&?)&?&?); subst.
        eapply Forall_forall in Henums; eauto. simpl in *.
        destruct t; simpl in *; auto.
        rewrite <-Heq; auto.
    Qed.

    Corollary wt_exps_wt_enum : forall vars es,
        Forall (wt_enum G) (map snd vars) ->
        Forall (wt_exp G vars) es ->
        Forall (wt_enum G) (typesof es).
    Proof.
      unfold typesof; induction es;
        intros * Henums Hwt; inv Hwt; simpl; auto.
      apply Forall_app; split; auto.
      eapply wt_exp_wt_enum; eauto.
    Qed.

  End wt_enum.

  (** ** wc implies wx *)

  Hint Constructors wx_exp wl_block.

  Fact wt_exp_wx_exp {PSyn prefs} (G: @global PSyn prefs) : forall vars e,
      wt_exp G vars e ->
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
        intros ? Hin. specialize (H _ Hin). specialize (H7 _ Hin).
        rewrite Forall_forall in *...
    - (* case *)
      constructor...
      + rewrite Forall_forall in *...
        intros ? Hin. specialize (H _ Hin); simpl in H. specialize (H10 _ Hin).
        rewrite Forall_forall in *...
      + intros ? Heq. inv Heq.
   - (* case *)
      constructor...
      + rewrite Forall_forall in *...
        intros ? Hin. specialize (H _ Hin); simpl in H. specialize (H11 _ Hin).
        rewrite Forall_forall in *...
      + intros ? Heq. inv Heq. simpl in *.
        rewrite Forall_forall in *...
    - (* app *)
      econstructor...
      + rewrite Forall_forall in *...
      + rewrite Forall_forall in *...
  Qed.
  Hint Resolve wt_exp_wx_exp.

  Corollary Forall_wt_exp_wx_exp {PSyn prefs} (G: @global PSyn prefs) : forall vars es,
      Forall (wt_exp G vars) es ->
      Forall (wx_exp (map fst vars)) es.
  Proof. intros. rewrite Forall_forall in *; eauto. Qed.
  Hint Resolve Forall_wt_exp_wx_exp.

  Fact wt_equation_wx_equation {PSyn prefs} (G: @global PSyn prefs) : forall vars equ,
      wt_equation G vars equ ->
      wx_equation (map fst vars) equ.
  Proof with eauto.
    intros vars [xs es] (Hwt1&Hwt2).
    constructor.
    + rewrite Forall_forall in *...
    + intros ? Hin.
      eapply Forall2_ignore2, Forall_forall in Hwt2 as (?&_&Hin'); eauto.
      eapply in_map_iff. now do 2 esplit; eauto.
  Qed.
  Hint Resolve wt_equation_wx_equation.

  Fact wt_block_wx_block {PSyn prefs} (G: @global PSyn prefs) : forall blk vars,
      wt_block G vars blk ->
      wx_block (map fst vars) blk.
  Proof.
    induction blk using block_ind2; intros * Wt; inv Wt; eauto.
    1-3:econstructor; eauto.
    1,2:rewrite Forall_forall in *; intros; eauto.
    rewrite <-map_fst_idty, <-map_fst_idty, <-map_app; eauto.
  Qed.
  Hint Resolve wt_block_wx_block.

  Fact wt_node_wx_node {PSyn prefs} : forall (G: @global PSyn prefs) n,
      wt_node G n ->
      wx_node n.
  Proof with eauto.
    intros G n (_&_&_&Hwt).
    unfold wx_node.
    rewrite <-map_fst_idty, <-map_fst_idty...
  Qed.
  Hint Resolve wt_node_wx_node.

  Fact wt_global_wx_global {PSyn prefs} : forall (G: @global PSyn prefs),
      wt_global G ->
      wx_global G.
  Proof with eauto.
    intros G (?&Hwt).
    unfold wt_global, wx_global, wt_program, units in *; simpl in *.
    induction Hwt...
    destruct H0...
  Qed.
  Hint Resolve wt_global_wx_global.

  (** Other useful stuff *)

  Lemma wt_clock_Is_free_in : forall x enums env ck,
      wt_clock enums env ck ->
      Is_free_in_clock x ck ->
      InMembers x env.
  Proof.
    induction ck; intros Hwt Hfree;
      inv Hwt; inv Hfree; eauto using In_InMembers.
  Qed.

  Corollary wt_nclock_Is_free_in : forall x enums env name ck,
      wt_nclock enums env (ck, name) ->
      Is_free_in_clock x ck ->
      InMembers x env.
  Proof.
    intros * Hwt Hin; inv Hwt. eapply wt_clock_Is_free_in; eauto.
  Qed.

End LTYPING.

Module LTypingFun
       (Ids   : IDS)
       (Op    : OPERATORS)
       (OpAux : OPERATORS_AUX Ids Op)
       (Cks   : CLOCKS Ids Op OpAux)
       (Syn   : LSYNTAX Ids Op OpAux Cks)
       <: LTYPING Ids Op OpAux Cks Syn.
  Include LTYPING Ids Op OpAux Cks Syn.
End LTypingFun.
