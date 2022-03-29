From Velus Require Import Common.
From Velus Require Import CommonProgram.
From Velus Require Import CommonTyping.
From Velus Require Import Operators.
From Velus Require Import Clocks.
From Velus Require Import Lustre.StaticEnv.
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
       (Import Senv  : STATICENV Ids Op OpAux Cks)
       (Import Syn   : LSYNTAX Ids Op OpAux Cks Senv).

  (** ** Clocks *)
  Section WellTyped.

    Variable enums : list (ident * nat).
    Variable Γ     : static_env.

    Inductive wt_clock : clock -> Prop :=
    | wt_Cbase:
        wt_clock Cbase
    | wt_Con: forall ck x tn c,
        HasType Γ x (Tenum tn) ->
        In tn enums ->
        c < snd tn ->
        wt_clock ck ->
        wt_clock (Con ck x (Tenum tn, c)).

  End WellTyped.

  Import Permutation.

  (** ** Expressions and equations *)
  Section WellTyped.
    Context {PSyn : block -> Prop}.
    Context {prefs : PS.t}.

    Variable G     : @global PSyn prefs.
    Variable Γ     : static_env.

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
        HasType Γ x ty ->
        wt_clock G.(enums) Γ nck ->
        wt_exp (Evar x (ty, nck))

    | wt_Elast: forall x ty nck,
        HasType Γ x ty ->
        IsLast Γ x ->
        wt_clock G.(enums) Γ nck ->
        wt_exp (Elast x (ty, nck))

    | wt_Eunop: forall op e tye ty nck,
        wt_exp e ->
        typeof e = [tye] ->
        type_unop op tye = Some ty ->
        wt_enum ty ->
        wt_clock G.(enums) Γ nck ->
        wt_exp (Eunop op e (ty, nck))

    | wt_Ebinop: forall op e1 e2 ty1 ty2 ty nck,
        wt_exp e1 ->
        wt_exp e2 ->
        typeof e1 = [ty1] ->
        typeof e2 = [ty2] ->
        type_binop op ty1 ty2 = Some ty ->
        wt_enum ty ->
        wt_clock G.(enums) Γ nck ->
        wt_exp (Ebinop op e1 e2 (ty, nck))

    | wt_Efby: forall e0s es anns,
        Forall wt_exp e0s ->
        Forall wt_exp es ->
        typesof es = map fst anns ->
        typesof e0s = map fst anns ->
        Forall (wt_clock G.(enums) Γ) (map snd anns) ->
        wt_exp (Efby e0s es anns)

    | wt_Earrow: forall e0s es anns,
        Forall wt_exp e0s ->
        Forall wt_exp es ->
        typesof es = map fst anns ->
        typesof e0s = map fst anns ->
        Forall (wt_clock G.(enums) Γ) (map snd anns) ->
        wt_exp (Earrow e0s es anns)

    | wt_Ewhen: forall es x b tn tys nck,
        HasType Γ x (Tenum tn) ->
        In tn G.(enums) ->
        b < snd tn ->
        Forall wt_exp es ->
        typesof es = tys ->
        wt_clock G.(enums) Γ nck ->
        wt_exp (Ewhen es x b (tys, nck))

    | wt_Emerge: forall x tn es tys nck,
        HasType Γ x (Tenum tn) ->
        In tn G.(enums) ->
        Permutation (map fst es) (seq 0 (snd tn)) ->
        es <> nil ->
        Forall (fun es => Forall wt_exp (snd es)) es ->
        Forall (fun es => typesof (snd es) = tys) es ->
        wt_clock G.(enums) Γ nck ->
        wt_exp (Emerge (x, Tenum tn) es (tys, nck))

    | wt_EcaseTotal: forall e es tn tys nck,
        wt_exp e ->
        typeof e = [Tenum tn] ->
        In tn G.(enums) ->
        Permutation (map fst es) (seq 0 (snd tn)) ->
        es <> nil ->
        Forall (fun es => Forall wt_exp (snd es)) es ->
        Forall (fun es => typesof (snd es) = tys) es ->
        wt_clock G.(enums) Γ nck ->
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
        wt_clock G.(enums) Γ nck ->
        wt_exp (Ecase e es (Some d) (tys, nck))

    | wt_Eapp: forall f es er anns n,
        Forall wt_exp es ->
        Forall wt_exp er ->
        find_node f G = Some n ->
        Forall2 (fun et '(_, (t, _, _)) => et = t) (typesof es) n.(n_in) ->
        Forall2 (fun a '(_, (t, _, _)) => fst a = t) anns n.(n_out) ->
        Forall (fun e => typeof e = [bool_velus_type]) er ->
        Forall (fun a => wt_clock G.(enums) Γ (snd a)) anns ->
        wt_exp (Eapp f es er anns).

    Definition wt_equation (eq : equation) : Prop :=
      let (xs, es) := eq in
      Forall wt_exp es
      /\ Forall2 (HasType Γ) xs (typesof es).

  End WellTyped.

  Definition wt_clocks enums (Γ : static_env) : list (ident * (type * clock * ident)) -> Prop :=
    Forall (fun '(_, (_, ck, _)) => wt_clock enums Γ ck).

  Inductive wt_scope {A} (P_wt : static_env -> A -> Prop) {PSyn prefs} (G: @global PSyn prefs) :
    static_env -> scope A -> Prop :=
  | wt_Scope : forall Γ Γ' locs blks,
      Γ' = Γ ++ senv_of_locs locs ->
      wt_clocks G.(enums) Γ' (Common.idty locs) ->
      Forall (wt_enum G) (map (fun '(_, (ty, _, _, _)) => ty) locs) ->
      Forall (fun '(_, (ty, _, _, o)) =>
                LiftO True (fun '(e, _) => wt_exp G Γ' e /\ typeof e = [ty]) o) locs ->
      P_wt Γ' blks ->
      wt_scope P_wt G Γ (Scope locs blks).

  Inductive wt_block {PSyn prefs} (G: @global PSyn prefs) : static_env -> block -> Prop :=
  | wt_Beq: forall Γ eq,
      wt_equation G Γ eq ->
      wt_block G Γ (Beq eq)

  | wt_Breset: forall Γ blocks er,
      Forall (wt_block G Γ) blocks ->
      wt_exp G Γ er ->
      typeof er = [bool_velus_type] ->
      wt_block G Γ (Breset blocks er)

  | wt_Bswitch : forall Γ ec branches tn,
      wt_exp G Γ ec ->
      typeof ec = [Tenum tn] ->
      In tn G.(enums) ->
      Permutation (map fst branches) (seq 0 (snd tn)) ->
      branches <> nil ->
      Forall (fun blks => wt_scope (fun Γ => Forall (wt_block G Γ)) G Γ (snd blks)) branches ->
      wt_block G Γ (Bswitch ec branches)

  | wt_Bauto : forall Γ ini oth states ck,
      wt_clock G.(enums) Γ ck ->
      Forall (fun '(e, t) => wt_exp G Γ e /\ typeof e = [bool_velus_type] /\ InMembers t states) ini ->
      InMembers oth states ->
      Permutation (map fst states) (seq 0 (length states)) ->
      states <> [] ->
      Forall (fun blks => wt_scope (fun Γ' blks => Forall (wt_block G Γ') (fst blks)
                                             /\ Forall (fun '(e, (t, _)) => wt_exp G Γ' e
                                                                        /\ typeof e = [bool_velus_type]
                                                                        /\ InMembers t states) (snd blks))
                                G Γ (snd blks)) states ->
      wt_block G Γ (Bauto ck (ini, oth) states)

  | wt_Blocal: forall Γ scope,
      wt_scope (fun Γ' => Forall (wt_block G Γ')) G Γ scope ->
      wt_block G Γ (Blocal scope).

  Definition wt_node {PSyn prefs} (G: @global PSyn prefs) (n: @node PSyn prefs) : Prop
    :=   wt_clocks G.(enums) (senv_of_inout n.(n_in)) n.(n_in)
       /\ wt_clocks G.(enums) (senv_of_inout (n.(n_in) ++ n.(n_out))) n.(n_out)
       /\ Forall (wt_enum G) (map (fun '(_, (ty, _, _)) => ty) (n.(n_in) ++ n.(n_out)))
       /\ wt_block G (senv_of_inout (n.(n_in) ++ n.(n_out))) n.(n_block).

  Definition wt_global {PSyn prefs} (G: @global PSyn prefs) : Prop :=
    In (bool_id, 2) G.(enums) /\
    wt_program wt_node G.

  Global Hint Constructors wt_clock wt_exp wt_block : ltyping.
  Global Hint Unfold wt_equation : ltyping.

  Section wt_exp_ind2.
    Context (PSyn : block -> Prop).
    Context (prefs : PS.t).

    Variable (G : @global PSyn prefs).
    Variable Γ : static_env.
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
        HasType Γ x ty ->
        wt_clock G.(enums) Γ nck ->
        P (Evar x (ty, nck)).

    Hypothesis ElastCase:
      forall x ty nck,
        HasType Γ x ty ->
        IsLast Γ x ->
        wt_clock G.(enums) Γ nck ->
        P (Elast x (ty, nck)).

    Hypothesis EunopCase:
      forall op e tye ty nck,
        wt_exp G Γ e ->
        P e ->
        typeof e = [tye] ->
        type_unop op tye = Some ty ->
        wt_enum G ty ->
        wt_clock G.(enums) Γ nck ->
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
        wt_clock G.(enums) Γ nck ->
        P (Ebinop op e1 e2 (ty, nck)).

    Hypothesis EfbyCase:
      forall e0s es anns,
        Forall (wt_exp G Γ) e0s ->
        Forall (wt_exp G Γ) es ->
        Forall P e0s ->
        Forall P es ->
        typesof es = map fst anns ->
        typesof e0s = map fst anns ->
        Forall (wt_clock G.(enums) Γ) (map snd anns) ->
        P (Efby e0s es anns).

    Hypothesis EarrowCase:
      forall e0s es anns,
        Forall (wt_exp G Γ) e0s ->
        Forall (wt_exp G Γ) es ->
        Forall P e0s ->
        Forall P es ->
        typesof es = map fst anns ->
        typesof e0s = map fst anns ->
        Forall (wt_clock G.(enums) Γ) (map snd anns) ->
        P (Earrow e0s es anns).

    Hypothesis EwhenCase:
      forall es x b tn tys nck,
        HasType Γ x (Tenum tn) ->
        In tn G.(enums) ->
        b < snd tn ->
        Forall (wt_exp G Γ) es ->
        Forall P es ->
        typesof es = tys ->
        wt_clock G.(enums) Γ nck ->
        P (Ewhen es x b (tys, nck)).

    Hypothesis EmergeCase:
      forall x es tn tys nck,
        HasType Γ x (Tenum tn) ->
        In tn G.(enums) ->
        Permutation (map fst es) (seq 0 (snd tn)) ->
        es <> nil ->
        Forall (fun es => Forall (wt_exp G Γ) (snd es)) es ->
        Forall (fun es => Forall P (snd es)) es ->
        Forall (fun es => typesof (snd es) = tys) es ->
        wt_clock G.(enums) Γ nck ->
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
        wt_clock G.(enums) Γ nck ->
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
        wt_clock G.(enums) Γ nck ->
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
        Forall (fun a => wt_clock G.(enums) Γ (snd a)) anns ->
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
    inversion 2; subst.
    eauto with ltyping datatypes senv.
  Qed.

  Global Instance wt_clock_Proper enums:
    Proper (@Permutation.Permutation _ ==> @eq clock ==> iff)
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

  Global Instance wt_clock_enums_Proper :
    Proper (@incl _ ==> @eq _ ==> @eq _ ==> Basics.impl) wt_clock.
  Proof.
    intros ?? Same ??? ? ck ? Wt; subst.
    induction ck; inversion_clear Wt; subst; repeat constructor; auto.
  Qed.

  Global Instance wt_clock_pointwise_Proper enums :
    Proper (@Permutation.Permutation _
                                     ==> pointwise_relation clock iff)
           (wt_clock enums).
  Proof.
    intros env' env Henv e.
    now rewrite Henv.
  Qed.

  Global Instance wt_clock_incl_Proper :
    Proper (@incl _ ==> @eq _ ==> @eq _ ==> Basics.impl) wt_clock.
  Proof.
    intros ?? Same ??? ? ck ? Wt; subst.
    rewrite Same in Wt; auto.
  Qed.

  Import Permutation.

  Global Instance wt_exp_Proper {PSyn prefs}:
    Proper (@eq (@global PSyn prefs) ==> @Permutation _
                ==> @eq exp ==> iff)
           wt_exp.
  Proof.
    intros G G' HG env' env Henv e' e He. subst.
    split; intro H;
      induction H using wt_exp_ind2;
      (rewrite Henv in * || rewrite <-Henv in * || idtac);
      try match goal with
          | H:Forall (fun a => wt_clock _ env' (snd a)) _ |- _ =>
            setoid_rewrite Henv in H
          | H:Forall (fun a => wt_clock _ env (snd a)) _ |- _ =>
            setoid_rewrite <-Henv in H
          end;
      eauto with ltyping;
      econstructor; eauto.
  Qed.

  Global Instance wt_exp_pointwise_Proper {PSyn prefs}:
    Proper (@eq (@global PSyn prefs) ==> @Permutation _
                                     ==> pointwise_relation exp iff) wt_exp.
  Proof.
    intros G G' HG ?? Henv ?.
    now rewrite HG, Henv.
  Qed.

  Global Instance wt_equation_Proper {PSyn prefs}:
    Proper (@eq (@global PSyn prefs) ==> @Permutation _
                ==> @eq equation ==> iff)
           wt_equation.
  Proof.
    intros G1 G2 HG ?? Henv eq1 eq2 Heq. subst.
    destruct eq2 as (xs & es).
    split; intros (WTeq1 & WTeq2); split; auto; simpl_Forall;
      (rewrite Henv || rewrite <-Henv); auto.
  Qed.

  (** Adding variables to the environment preserves typing *)

  Section incl.

    Fact wt_clock_incl : forall enums Γ Γ' cl,
        (forall x ty, HasType Γ x ty -> HasType Γ' x ty) ->
        wt_clock enums Γ cl ->
        wt_clock enums Γ' cl.
    Proof.
      intros * Hincl Hwt.
      induction Hwt.
      - constructor.
      - constructor; eauto with senv.
    Qed.
    Local Hint Resolve wt_clock_incl : ltyping.

    Lemma wt_exp_incl {PSyn prefs} : forall (G: @global PSyn prefs) Γ Γ' e,
        (forall x ty, HasType Γ x ty -> HasType Γ' x ty) ->
        (forall x, IsLast Γ x -> IsLast Γ' x) ->
        wt_exp G Γ e ->
        wt_exp G Γ' e.
    Proof.
      intros * Hincl1 Hincl2 Hwt.
      induction Hwt using wt_exp_ind2;
        econstructor; eauto with senv ltyping.
      1-2:eapply Forall_impl; [| eauto]; intros; eauto with ltyping.
      (* app *)
      eapply Forall_impl; [| eauto].
      intros; simpl in *; eauto using incl_map with ltyping.
    Qed.

    Lemma wt_equation_incl {PSyn prefs} : forall (G: @global PSyn prefs) Γ Γ' eq,
        (forall x ty, HasType Γ x ty -> HasType Γ' x ty) ->
        (forall x, IsLast Γ x -> IsLast Γ' x) ->
        wt_equation G Γ eq ->
        wt_equation G Γ' eq.
    Proof.
      intros * Hincl1 Hincl2 Hwt.
      destruct eq; simpl in *. destruct Hwt as [Hwt1 Hwt2].
      split.
      - eapply Forall_impl; [| eauto].
        intros. eapply wt_exp_incl; eauto.
      - simpl_Forall; eauto with senv.
    Qed.

    Lemma wt_scope_incl {A} (P_wt : static_env -> A -> Prop) {PSyn prefs} : forall (G: @global PSyn prefs) Γ Γ' locs blks,
        (forall x ty, HasType Γ x ty -> HasType Γ' x ty) ->
        (forall x, IsLast Γ x -> IsLast Γ' x) ->
        (forall Γ Γ', (forall x ty, HasType Γ x ty -> HasType Γ' x ty) ->
                 (forall x, IsLast Γ x -> IsLast Γ' x) ->
                 P_wt Γ blks ->
                 P_wt Γ' blks) ->
        wt_scope P_wt G Γ (Scope locs blks) ->
        wt_scope P_wt G Γ' (Scope locs blks).
    Proof.
      intros * Hty Hl Hp Hwt.
      assert (forall x ty, HasType (Γ ++ senv_of_locs locs) x ty -> HasType (Γ' ++ senv_of_locs locs) x ty) as Hty'.
      { intros *. rewrite 2 HasType_app. intros [|]; auto. }
      assert (forall x, IsLast (Γ ++ senv_of_locs locs) x -> IsLast (Γ' ++ senv_of_locs locs) x) as Hl'.
      { intros *. rewrite 2 IsLast_app. intros [|]; auto. }
      inv Hwt. econstructor; eauto.
      - unfold wt_clocks in *; simpl_Forall; eauto using wt_clock_incl.
      - simpl_Forall.
        destruct o as [(?&?)|]; simpl in *; destruct_conjs; split; eauto using wt_exp_incl.
    Qed.

    Lemma wt_block_incl {PSyn prefs} : forall (G: @global PSyn prefs) d Γ Γ',
        (forall x ty, HasType Γ x ty -> HasType Γ' x ty) ->
        (forall x, IsLast Γ x -> IsLast Γ' x) ->
        wt_block G Γ d ->
        wt_block G Γ' d .
    Proof.
      induction d using block_ind2; intros * Incl1 Incl2 Wt; inv Wt.
      - constructor. eauto using wt_equation_incl.
      - econstructor; eauto using wt_exp_incl.
        simpl_Forall; eauto.
      - econstructor; eauto using wt_exp_incl.
        simpl_Forall; eauto.
        destruct s. eapply wt_scope_incl; eauto.
        intros * Hty' Hl' ?; simpl_Forall; eauto using wt_exp_incl.
      - econstructor; auto; simpl_Forall; eauto using wt_exp_incl, wt_clock_incl.
        destruct s. eapply wt_scope_incl; eauto.
        intros * Hty' Hl' (?&?); split; simpl_Forall; eauto using wt_exp_incl.
      - econstructor.
        eapply wt_scope_incl; eauto.
        intros; simpl_Forall; eauto.
    Qed.

  End incl.

  (* Local Hint Resolve wt_clock_incl incl_appl incl_refl : core. *)
  Lemma wt_exp_clockof {PSyn prefs}:
    forall (G: @global PSyn prefs) Γ e,
      wt_exp G Γ e ->
      Forall (wt_clock G.(enums) Γ) (clockof e).
  Proof.
    intros * Hwt.
    apply Forall_forall. intros ck Hin.
    inv Hwt; simpl in *.
    - destruct Hin as [Hin|]; [|contradiction].
      rewrite <-Hin; auto with ltyping.
    - destruct Hin as [Hin|]; [|contradiction].
      rewrite <-Hin; auto with ltyping.
    - destruct Hin as [Hin|]; [|contradiction].
      rewrite <-Hin; auto.
    - destruct Hin as [Hin|]; [|contradiction].
      rewrite <-Hin; auto.
    - destruct Hin as [Hin|]; [|contradiction].
      rewrite <-Hin; auto.
    - destruct Hin as [Hin|]; [|contradiction].
      rewrite <-Hin; auto.
    - simpl_In. simpl_Forall. eauto.
    - simpl_In. simpl_Forall. eauto.
    - simpl_In; eauto.
    - simpl_In; eauto.
    - simpl_In; eauto.
    - simpl_In; eauto.
    - simpl_In. simpl_Forall. eauto.
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

  Lemma check_clock_correct:
    forall eenv venv env ck,
      (forall x ty, Env.find x venv = Some ty -> HasType env x ty) ->
      check_clock eenv venv ck = true ->
      wt_clock (Env.elements eenv) env ck.
  Proof.
    induction ck; intros Hfind CC. now constructor.
    simpl in CC. cases_eqn Heq; subst.
    - repeat rewrite Bool.andb_true_iff in CC; destruct CC as (CC1 & (CC2 & CC3) & CC4).
      apply IHck in CC4; auto. rewrite equiv_decb_equiv in CC1; inv CC1.
      rewrite equiv_decb_equiv in CC2; inv CC2.
      apply Env.elements_correct in Heq3.
      apply Nat.ltb_lt in CC3.
      constructor; auto.
    - rewrite Bool.andb_false_r in CC. congruence.
  Qed.

  Ltac solve_ndup :=
    unfold idty in *; simpl in *; solve_NoDupMembers_app.

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
      eapply Sorted_impl, SortNat.Sorted_sort.
      intros ?? Hle; simpl in *. inv Hle.
      apply Nat.leb_le; auto.
  Qed.

  Section ValidateExpression.
    Context {PSyn : block -> Prop}.
    Context {prefs : PS.t}.

    Variable G : @global PSyn prefs.
    Variable eenv : Env.t nat.
    Variable venv venvl : Env.t type.
    Variable env : static_env.

    Hypothesis Henums : incl (Env.elements eenv) G.(enums).
    Hypothesis Henv : forall x ty, Env.find x venv = Some ty -> HasType env x ty.
    Hypothesis Henvl : forall x ty, Env.find x venvl = Some ty -> HasType env x ty /\ IsLast env x.

    Open Scope option_monad_scope.

    Definition check_paired_types2 (t1 : type) (tc : ann) : bool :=
      let '(t, c) := tc in
      (t1 ==b t) && (check_clock eenv venv c).

    Definition check_paired_types3 (t1 t2 : type) (tc : ann) : bool :=
      let '(t, c) := tc in
      (t1 ==b t) && (t2 ==b t) && (check_clock eenv venv c).

    Definition check_reset (tr : list (list type)) : bool :=
      forallb (fun tys => match tys with [ty] => ty ==b bool_velus_type | _ => false end) tr.

    Definition check_var (x : ident) (ty : type) : bool :=
      match Env.find x venv with
      | Some xt => ty ==b xt
      | None => false
      end.

    Definition check_last (x : ident) (ty : type) : bool :=
      match Env.find x venvl with
      | Some xt => ty ==b xt
      | _ => false
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
        if check_var x xt && check_clock eenv venv nck then Some [xt] else None

      | Elast x (xt, nck) =>
        if check_last x xt && check_clock eenv venv nck then Some [xt] else None

      | Eunop op e (xt, nck) =>
        do te <- assert_singleton (check_exp e);
        do t <- type_unop op te;
        if (xt ==b t) && check_enum t && check_clock eenv venv nck then Some [xt] else None

      | Ebinop op e1 e2 (xt, nck) =>
        do te1 <- assert_singleton (check_exp e1);
        do te2 <- assert_singleton (check_exp e2);
        do t <- type_binop op te1 te2;
        if (xt ==b t) && check_enum t && check_clock eenv venv nck then Some [xt] else None

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
          if check_enum (Tenum (xt, n)) && (k <? n) && (forall2b equiv_decb ts tys) && (check_clock eenv venv nck)
          then Some tys else None
        | _ => None
        end

      | Emerge (x, Tenum (xt, n)) es (tys, nck) =>
        do tss <- omap (fun es => oconcat (map check_exp (snd es))) es;
        if check_var x (Tenum (xt, n)) && check_enum (Tenum (xt, n))
           && (check_perm_seq (map fst es) n) && (negb (is_nil es))
           && (forallb (fun ts => forall2b equiv_decb ts tys) tss)
           && (check_clock eenv venv nck)
        then Some tys else None

      | Ecase e brs None (tys, nck) =>
        do tss <- omap (fun es => oconcat (map check_exp (snd es))) brs;
        (* do tds <- oconcat (map check_exp d); *)
        do xt <- assert_singleton (check_exp e);
        match xt with
        | Tenum (xt, n) =>
          if check_enum (Tenum (xt, n))
             && (check_perm_seq (map fst brs) n) && (negb (is_nil brs))
             && (forallb (fun ts => (forall2b equiv_decb ts tys)) tss)
             && (check_clock eenv venv nck)
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
             && (check_nodup_nat (map fst brs)) && (forallb (fun i => i <? n) (map fst brs)) && (negb (is_nil brs))
             && (forallb (fun ts => (forall2b equiv_decb ts tys)) (tds::tss))
             && (check_clock eenv venv nck)
          then Some tys else None
        | _ => None
        end

      | Eapp f es er anns =>
        do n <- find_node f G;
        do ts <- oconcat (map check_exp es);
        do tr <- omap check_exp er;
        if (forall2b (fun et '(_, (t, _, _)) => et ==b t) ts n.(n_in))
             && (forall2b (fun '(ot, oc) '(_, (t, _, _)) =>
                             check_clock eenv venv oc
                             && (ot ==b t)) anns n.(n_out))
             && check_reset tr
        then Some (map fst anns)
        else None

      | _ => None
      end.

    Definition check_equation (eq : equation) : bool :=
      let '(xs, es) := eq in
      match oconcat (map check_exp es) with
      | None => false
      | Some tys => forall2b check_var xs tys
      end.

    Lemma check_var_correct:
      forall x ty,
        check_var x ty = true ->
        HasType env x ty.
    Proof.
      intros * Hc. unfold check_var in *.
      cases_eqn Heq; simpl.
      rewrite equiv_decb_equiv in Hc. inv Hc. auto.
    Qed.
    (* Local Hint Resolve check_var_correct : ltyping. *)

    Lemma check_last_correct:
      forall x ty,
        check_last x ty = true ->
        HasType env x ty /\ IsLast env x.
    Proof.
      intros * Hc. unfold check_last in *.
      cases_eqn Heq; simpl.
      rewrite equiv_decb_equiv in Hc. inv Hc. auto.
    Qed.

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
    (* Local Hint Resolve check_enum_correct' : ltyping. *)

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
    (* Local Hint Resolve check_enum_correct : ltyping. *)

    Lemma check_paired_types2_correct:
      forall tys1 anns,
        forall2b check_paired_types2 tys1 anns = true ->
        tys1 = map fst anns
        /\ Forall (wt_clock G.(enums) env) (map snd anns).
    Proof.
      setoid_rewrite forall2b_Forall2.
      induction 1 as [|ty1 (ty, nck) tys1 anns IH1 IH3];
        subst; simpl; eauto.
      simpl in IH1.
      repeat rewrite Bool.andb_true_iff in IH1.
      setoid_rewrite equiv_decb_equiv in IH1.
      destruct IH1 as (-> & IH1).
      eapply check_clock_correct in IH1; eauto. rewrite Henums in IH1.
      destruct IHIH3; split; try f_equal; auto.
    Qed.

    Lemma check_paired_types3_correct:
      forall tys1 tys2 anns,
        forall3b check_paired_types3 tys1 tys2 anns = true ->
        tys1 = map fst anns
        /\ tys2 = map fst anns
        /\ Forall (wt_clock G.(enums) env) (map snd anns).
    Proof.
      setoid_rewrite forall3b_Forall3.
      induction 1 as [|ty1 ty2 (ty, nck) tys1 tys2 anns IH1 IH2 (? & ? & IH3)];
        subst; simpl; eauto.
      simpl in IH1.
      repeat rewrite Bool.andb_true_iff in IH1.
      setoid_rewrite equiv_decb_equiv in IH1.
      destruct IH1 as ((-> & ->) & IH1).
      eapply check_clock_correct in IH1; eauto. rewrite Henums in IH1. auto.
    Qed.

    Lemma oconcat_map_check_exp':
      forall {f} es tys,
        (forall e tys,
            In e es ->
            f e = Some tys ->
            wt_exp G env e /\ typeof e = tys) ->
        oconcat (map f es) = Some tys ->
        Forall (wt_exp G env) es
        /\ typesof es = tys.
    Proof.
      induction es as [|e es IH]; intros tys WTf CE. now inv CE; auto.
      simpl in CE. destruct (f e) eqn:Ce; [|now omonadInv CE].
      destruct (oconcat (map f es)) as [tes|]; [|now omonadInv CE].
      omonadInv CE. simpl.
      apply WTf in Ce as (Ce1 & ->); auto with datatypes.
      destruct (IH tes) as (? & ->); auto.
      intros * Ies Fe. apply WTf in Fe; auto with datatypes.
    Qed.

    Lemma omap_concat_map_check_exp':
      forall {f} (ess : list (enumtag * _)) tys,
        (forall es e tys,
            In es ess ->
            In e (snd es) ->
            f e = Some tys ->
            wt_exp G env e /\ typeof e = tys) ->
        omap (fun es => oconcat (map f (snd es))) ess = Some tys ->
        Forall (fun es => Forall (wt_exp G env) (snd es)) ess
        /\ Forall2 (fun es tys => typesof (snd es) = tys) ess tys.
    Proof with try solve_ndup.
      induction ess as [|es ess IH]; intros tys WTf CE. now inv CE; auto.
      simpl in CE. destruct (oconcat (map f (snd es))) eqn:Ce; [|now omonadInv CE].
      eapply oconcat_map_check_exp' in Ce as (?&?); eauto with datatypes...
      destruct (omap _ _) as [tes|]; [|now omonadInv CE]...
      omonadInv CE. simpl.
      specialize (IH tes) as (? & ?); eauto using in_cons...
    Qed.

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
            f e = Some tys ->
            wt_exp G env e /\ typeof e = tys) ->
        omap f es = Some tys ->
        Forall (wt_exp G env) es
        /\ Forall2 (fun e ty => typeof e = ty) es tys.
    Proof with try solve_ndup.
      induction es as [|e es IH]; intros tys WTf CE. now inv CE; auto.
      simpl in CE. destruct (f e) eqn:Ce; [|now omonadInv CE].
      destruct (omap f es) as [tes|]; [|now omonadInv CE].
      omonadInv CE. simpl.
      apply WTf in Ce as (Ce1 & ?); auto with datatypes...
      destruct (IH tes) as (? & ?); auto with datatypes...
    Qed.

    Import Permutation.
    Local Hint Constructors wt_exp wt_block : ltyping.
    Lemma check_exp_correct:
      forall e tys,
        check_exp e = Some tys ->
        wt_exp G env e
        /\ typeof e = tys.
    Proof with eauto with ltyping.
      induction e using exp_ind2; simpl; intros tys CE. 11:destruct d; simpl in *.
      1-13:repeat progress
               match goal with
               | a:ann |- _ => destruct a
               | a:lann |- _ => destruct a
               | p:type * clock |- _ => destruct p
               | p:_ * bool |- _ => destruct p
               | x:ident * type |- _ => destruct x
               | H:obind _ _ = Some _ |- _ => omonadInv H
               | H:obind2 _ _ = Some _ |- _ => omonadInv H
               | H:obind ?v _ = Some _ |- _ =>
                 let OE:=fresh "OE0" in destruct v eqn:OE; [simpl in H|now omonadInv H]
               | H: _ && _ = true |- _ => apply Bool.andb_true_iff in H as (? & ?)
               | H: ((_ ==b _) = true) |- _ => rewrite equiv_decb_equiv in H; inv H
               | H: check_clock _ _ _ = true |- _ => eapply check_clock_correct in H; eauto; rewrite Henums in H
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
               | H:check_var _ _ = true |- _ => eapply check_var_correct in H; eauto
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
      - (* Elast *)
        eapply check_last_correct in H as (?&?)...
      - (* Eunop *)
        apply IHe in OE0 as (? & ?)...
      - (* Ebinop *)
        apply IHe1 in OE0 as (? & ?); apply IHe2 in OE1 as (? & ?)...
      - (* Efby *)
        take (Forall _ e0s) and rewrite Forall_forall in it.
        take (Forall _ es) and rewrite Forall_forall in it.
        apply oconcat_map_check_exp' in OE0 as (? & ?)...
        apply oconcat_map_check_exp' in OE1 as (? & ?)...
        repeat constructor; eauto. 1,2:congruence.
      - (* Earrow *)
        take (Forall _ e0s) and rewrite Forall_forall in it.
        take (Forall _ es) and rewrite Forall_forall in it.
        apply oconcat_map_check_exp' in OE0 as (? & ?)...
        apply oconcat_map_check_exp' in OE1 as (? & ?)...
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
        + contradict H3; subst; simpl. auto.
        + eapply Forall2_ignore2 in Hty.
          eapply Forall_impl; [|eapply Hty]; intros (?&?) (?&Hin&Hty').
          eapply Forall_forall in H2; eauto. simpl in *; congruence.
      - (* Ecase *)
        take (check_exp _ = Some _) and apply IHe in it as (? & ?).
        take (Forall _ es) and (repeat setoid_rewrite Forall_forall in it).
        take (omap _ _ = Some _) and
             apply omap_concat_map_check_exp' in it as (Hwt & Hty); eauto.
        take (Forall _ l) and (repeat setoid_rewrite Forall_forall in it).
        eapply oconcat_map_check_exp' in OE1 as (? & ?)...
        do 2 econstructor; eauto.
        + apply check_enum_correct' in H1 as (?&?)...
        + intros ? Hin.
          eapply forallb_Forall, Forall_forall in H6; eauto. eapply Nat.ltb_lt in H6.
          eapply in_seq. split; simpl; lia.
        + eapply check_nodup_nat_NoDup, fst_NoDupMembers in H7...
        + contradict H5; subst; simpl. auto.
        + eapply Forall2_ignore2 in Hty.
          eapply Forall_impl; [|eapply Hty]; intros (?&?) (?&Hin&Hty').
          eapply Forall_forall in H4; eauto. simpl in *; congruence.
        + congruence.
      - (* Ecase *)
        take (check_exp _ = Some _) and apply IHe in it as (? & ?).
        take (Forall _ es) and (repeat setoid_rewrite Forall_forall in it).
        take (omap _ _ = Some _) and
             apply omap_concat_map_check_exp' in it as (Hwt & Hty); eauto.
        do 2 econstructor; eauto.
        + apply check_enum_correct' in H1 as (?&?)...
        + eapply check_perm_seq_spec in H5...
        + contradict H4; subst; simpl. auto.
        + eapply Forall2_ignore2 in Hty.
          eapply Forall_impl; [|eapply Hty]; intros (?&?) (?&Hin&Hty').
          eapply Forall_forall in H3; eauto. simpl in *; congruence.
      - (* Eapp *)
        take (Forall _ es) and rewrite Forall_forall in it.
        take (Forall _ er) and rewrite Forall_forall in it.
        take (oconcat (map check_exp _) = Some _) and
             apply oconcat_map_check_exp' in it as (? & ?); auto.
        take (omap check_exp _ = Some _) and
             apply omap_check_exp' in it as (? & ?); auto.
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
        assert (Forall (fun ann => wt_clock G.(enums) env (snd ann)) a).
        { repeat take (Forall2 _ _ n.(n_out)) and apply Forall2_ignore2 in it.
          apply Forall_impl_In with (2:=it).
          intros (? & ?) ? ((? & ((?&?)&?)) & (? & EQ)); simpl.
          apply Bool.andb_true_iff in EQ as (EQ1 & EQ2).
          eapply check_clock_correct in EQ1; eauto. rewrite Henums in EQ1; auto.
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
        oconcat (map check_exp es) = Some tys ->
        Forall (wt_exp G env) es
        /\ typesof es = tys.
    Proof.
      intros.
      eapply oconcat_map_check_exp'; eauto.
      intros. eapply check_exp_correct; eauto.
    Qed.

    Corollary omap_check_exp:
      forall es tys,
        omap check_exp es = Some tys ->
        Forall (wt_exp G env) es
        /\ Forall2 (fun e ty => typeof e = ty) es tys.
    Proof.
      intros.
      eapply omap_check_exp'; eauto.
      intros. eapply check_exp_correct; eauto.
    Qed.

    Lemma check_equation_correct:
      forall eq,
        check_equation eq = true ->
        wt_equation G env eq.
    Proof.
      intros eq CE. destruct eq as (xs, es); simpl in CE.
      cases_eqn Heq.
      take (oconcat (map check_exp _) = Some _)
           and apply oconcat_map_check_exp in it as (? & ?).
      take (forall2b check_var _ _ = true)
           and apply forall2b_Forall2 in it.
      subst; constructor; auto.
      simpl_Forall. eapply check_var_correct; eauto.
    Qed.

  End ValidateExpression.

  Section ValidateBlock.
    Context {PSyn : block -> Prop}.
    Context {prefs : PS.t}.
    Variable (G : @global PSyn prefs).

    Variable (eenv : Env.t nat).
    Hypothesis Henums : incl (Env.elements eenv) G.(enums).

    Definition check_tag {A} (l : list (enumtag * A)) (x : enumtag) :=
      existsb (fun '(y, _) => x =? y) l.

    Lemma check_tag_correct {A} : forall (l : list (_ * A)) x,
        check_tag l x = true ->
        InMembers x l.
    Proof.
      intros * Hc. unfold check_tag in Hc.
      rewrite <-Exists_existsb with (P:=fun y => x = fst y) in Hc.
      2:intros; destruct_conjs; simpl; rewrite Nat.eqb_eq; reflexivity.
      simpl_Exists; subst; eauto using In_InMembers.
    Qed.

    Definition check_bool_exp venv venvl e :=
      match check_exp G eenv venv venvl e with
      | Some [tyr] => tyr ==b bool_velus_type
      | _ => false
      end.

    Lemma check_bool_exp_correct venv venvl env : forall e,
        (forall x ty, Env.find x venv = Some ty -> HasType env x ty) ->
        (forall x ty, Env.find x venvl = Some ty -> HasType env x ty /\ IsLast env x) ->
        check_bool_exp venv venvl e = true ->
        wt_exp G env e /\ typeof e = [bool_velus_type].
    Proof.
      intros * Henv Henvl Hc. unfold check_bool_exp in Hc.
      cases_eqn Hc.
      eapply check_exp_correct in Hc0 as (Hwc&?); eauto.
      rewrite equiv_decb_equiv in Hc. inv Hc.
      auto.
    Qed.

    Definition check_scope {A} (f_check : Env.t type -> Env.t type -> A -> bool)
               (venv venvl : Env.t type) (s : scope A) : bool :=
      let 'Scope locs blks := s in
      let venv' := Env.union venv (Env.from_list (map (fun '(x, (ty, _, _, _)) => (x, ty)) locs)) in
      let venvl' := Env.union venvl (Env.from_list (map_filter (fun '(x, (ty, _, _, o)) => option_map (fun _ => (x, ty)) o) locs)) in
      forallb (check_clock eenv venv') (map (fun '(_, (_, ck, _, _)) => ck) locs)
      && forallb (check_enum eenv) (map (fun '(x, (ty, _, _, _)) => ty) locs)
      && forallb (fun '(_, (ty, _, _, o)) => match o with
                                          | None => true
                                          | Some (e, _) => match check_exp G eenv venv' venvl' e with
                                                          | Some [ty'] => ty' ==b ty
                                                          | _ => false
                                                          end
                                          end) locs
      && f_check venv' venvl' blks.

    Fixpoint check_block (venv venvl : Env.t type) (d : block) : bool :=
      match d with
      | Beq eq => check_equation G eenv venv venvl eq
      | Breset blocks er =>
          forallb (check_block venv venvl) blocks
          && check_bool_exp venv venvl er
      | Bswitch ec brs =>
        match assert_singleton (check_exp G eenv venv venvl ec) with
        | Some (Tenum (xt, n)) =>
            check_enum eenv (Tenum (xt, n))
            && check_perm_seq (map fst brs) n
            && (negb (is_nil brs))
            && forallb (fun '(_, blks) =>
                          check_scope (fun venv' venvl' =>
                                         forallb (check_block venv' venvl')) venv venvl blks) brs
        | _ => false
        end
      | Bauto ck (ini, oth) states =>
          check_clock eenv venv ck
          && forallb (fun '(e, t) => check_bool_exp venv venvl e && check_tag states t) ini
          && check_tag states oth
          && check_perm_seq (map fst states) (length states)
          && (negb (is_nil states))
          && forallb (fun '(_, blks) =>
                        check_scope (fun venv' venvl' '(blks, trans) =>
                                       forallb (check_block venv' venvl') blks
                                       && forallb (fun '(e, (t, _)) => check_bool_exp venv' venvl' e
                                                                    && check_tag states t) trans) venv venvl blks) states
      | Blocal s =>
          check_scope (fun venv' venvl' => forallb (check_block venv' venvl')) venv venvl s
      end.

    Hint Constructors wt_block : ltyping.
    Import Permutation.

    Opaque check_enum.

    Fact check_scope_correct {A} f_check (P_wt : _ -> _ -> Prop) : forall locs (blks: A) venv venvl env,
        (forall x ty, Env.find x venv = Some ty -> HasType env x ty) ->
        (forall x ty, Env.find x venvl = Some ty -> HasType env x ty /\ IsLast env x) ->
        (forall venv venvl env,
            (forall x ty, Env.find x venv = Some ty -> HasType env x ty) ->
            (forall x ty, Env.find x venvl = Some ty -> HasType env x ty /\ IsLast env x) ->
            f_check venv venvl blks = true ->
            P_wt env blks) ->
        check_scope f_check venv venvl (Scope locs blks) = true ->
        wt_scope P_wt G env (Scope locs blks).
    Proof.
      intros * Henv Henvl Hp Hc.
      assert (forall x ty, Env.find x (Env.union venv (Env.from_list (map (fun '(x0, (ty0, _, _, _)) => (x0, ty0)) locs))) = Some ty ->
                        HasType (env ++ senv_of_locs locs) x ty) as Henv'.
        { intros * Hfind. apply Env.union_find4 in Hfind as [Hfind|Hfind].
          - apply Henv in Hfind. inv Hfind. eauto with senv datatypes.
          - apply Env.from_list_find_In in Hfind. simpl_In.
            econstructor. apply in_or_app, or_intror. solve_In.
            reflexivity.
        }
        assert (forall x ty,
                   Env.find x (Env.union venvl (Env.from_list (map_filter (fun '(x0, (ty0, _, _, o)) => option_map (fun _ : exp * ident => (x0, ty0)) o) locs))) = Some ty ->
                   HasType (env ++ senv_of_locs locs) x ty /\ IsLast (env ++ senv_of_locs locs) x) as Henvl'.
        { intros * Hfind. apply Env.union_find4 in Hfind as [Hfind|Hfind].
          - apply Henvl in Hfind as (Hhas&His). inv Hhas. inv His.
            constructor; eauto with senv datatypes.
          - apply Env.from_list_find_In in Hfind. simpl_In.
            split; econstructor; try apply in_or_app, or_intror; solve_In.
            reflexivity. simpl. congruence.
        }
        simpl in *.
      repeat rewrite Bool.andb_true_iff in Hc. destruct Hc as (((CC&CE)&CL)&CB).
      apply forallb_Forall in CC. apply forallb_Forall in CE. apply forallb_Forall in CL.
      econstructor; eauto.
      - unfold Common.idty, wt_clocks. simpl_Forall.
        eapply check_clock_correct in CC; eauto. rewrite Henums in CC; eauto.
      - simpl_Forall. eapply check_enum_correct; eauto.
      - simpl_Forall. destruct o as [(?&?)|]; simpl in *; auto.
        cases_eqn EQ; subst.
        rewrite equiv_decb_equiv in CL; inv CL.
        eapply check_exp_correct in EQ as (Hwt&Hty); eauto.
    Qed.

    Lemma check_block_correct : forall blk venv venvl env,
        (forall x ty, Env.find x venv = Some ty -> HasType env x ty) ->
        (forall x ty, Env.find x venvl = Some ty -> HasType env x ty /\ IsLast env x) ->
        check_block venv venvl blk = true ->
        wt_block G env blk.
    Proof.
      Opaque check_scope.
      induction blk using block_ind2; intros * Henv Henvl CD; simpl in *.
      - (* equation *)
        eapply check_equation_correct in CD; eauto with ltyping.
      - (* reset *)
        eapply Bool.andb_true_iff in CD as (CDs&CE).
        eapply forallb_Forall in CDs.
        eapply check_bool_exp_correct in CE as (Wte&Tye); eauto.
        econstructor; eauto.
        simpl_Forall; eauto.
      - (* switch *)
        cases_eqn EQ; subst.
        eapply assert_singleton_spec, check_exp_correct in EQ as (Hwt1&Hty1); auto.
        repeat rewrite Bool.andb_true_iff in CD. destruct CD as (((CE&CP)&CL)&CBrs).
        eapply check_enum_correct in CE as (?&?); simpl in *; eauto.
        econstructor; eauto.
        + eapply check_perm_seq_spec; eauto.
        + contradict CL; subst; simpl in *. auto.
        + eapply forallb_Forall in CBrs. simpl_Forall.
          destruct s. eapply check_scope_correct; eauto.
          intros; simpl in *.
          eapply forallb_Forall in H5. simpl_Forall; eauto.
      - (* automaton *)
        destruct_conjs. repeat rewrite Bool.andb_true_iff in CD.
        destruct CD as (((((CC&CI)&CO)&CP)&CN)&CB).
        repeat (take (forallb _ _ = true) and apply forallb_Forall in it).
        constructor; eauto using check_tag_correct; simpl_Forall.
        + eapply check_clock_correct in CC; eauto.
          eapply wt_clock_enums_Proper; eauto.
        + apply Bool.andb_true_iff in it as (Hce&Htag).
          eapply check_bool_exp_correct in Hce as (?&?); eauto using check_tag_correct.
        + apply check_perm_seq_spec; auto.
        + contradict CN; subst; simpl in *. auto.
        + destruct s as [?(?&?)]. eapply check_scope_correct; eauto.
          intros * ?? Hc; simpl in *.
          rewrite Bool.andb_true_iff, 2 forallb_Forall in Hc. destruct Hc as (?&CT).
          split; simpl_Forall; eauto.
          apply Bool.andb_true_iff in CT as (CE&?).
          eapply check_bool_exp_correct in CE as (?&?); eauto using check_tag_correct.
      - (* local *)
        constructor. eapply check_scope_correct; eauto.
        intros * ?? Hc. apply forallb_Forall in Hc.
        simpl_Forall; eauto.
        Transparent check_scope.
    Qed.
  End ValidateBlock.

  Section ValidateGlobal.
    Definition check_node {PSyn prefs} (G : @global PSyn prefs) eenv (n : @node PSyn prefs) :=
      let ins := List.map (fun '(x, (ty, _, _)) => (x, ty)) (n_in n) in
      let insouts := List.map (fun '(x, (ty, _, _)) => (x, ty)) (n_in n ++ n_out n) in
      forallb (check_clock eenv (Env.from_list ins)) (List.map (fun '(_, (_, ck, _)) => ck) (n_in n)) &&
      forallb (check_clock eenv (Env.from_list insouts)) (List.map (fun '(_, (_, ck, _)) => ck) (n_out n)) &&
      forallb (check_enum eenv) (map snd insouts) &&
      check_block G eenv (Env.from_list insouts) (@Env.empty _) (n_block n).

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
      assert (forall x ty, Env.find x (Env.from_list (map (fun '(x0, (ty0, _, _)) => (x0, ty0)) (n_in n ++ n_out n))) = Some ty ->
                      HasType (senv_of_inout (n_in n ++ n_out n)) x ty) as Henv.
      { intros * Hfind. apply Env.from_list_find_In in Hfind. simpl_In.
          econstructor. solve_In. reflexivity. }
      split; [|split; [|split]].
      1-2:(unfold wt_clocks; simpl_Forall;
           take (check_clock _ _ _ = _) and eapply check_clock_correct in it; eauto;
           try rewrite Hincl in it; eauto).
      1:{ intros * Hfind. apply Env.from_list_find_In in Hfind. simpl_In.
          econstructor. solve_In. reflexivity. }
      - simpl_Forall. eapply check_enum_correct; eauto.
      - eapply check_block_correct in Hc4; eauto.
        intros * Hfind. exfalso. rewrite Env.gempty in Hfind. congruence.
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
      1-2:simpl in Hcheck; apply Bool.andb_true_iff in Hcheck as [Hc1 Hc2]; auto.
      split.
      - apply check_node_correct in Hc1; auto using Env.elements_from_list_incl.
      - apply Forall_forall. intros ? Hin contra.
        apply H1. rewrite in_map_iff. exists x; split; auto.
    Qed.
  End ValidateGlobal.

  Section interface_incl.
    Context {PSyn1 PSyn2 : block -> Prop}.
    Context {prefs1 prefs2 : PS.t}.
    Variable G1 : @global PSyn1 prefs1.
    Variable G2 : @global PSyn2 prefs2.

    Hypothesis Heq : global_iface_incl G1 G2.

    Fact iface_incl_wt_clock : forall vars ck,
        wt_clock G1.(enums) vars ck ->
        wt_clock G2.(enums) vars ck.
    Proof.
      induction ck; intros * Hwt; inv Hwt; constructor; auto.
      apply Heq; auto.
    Qed.

    Lemma iface_incl_wt_enum : forall ty,
        wt_enum G1 ty ->
        wt_enum G2 ty.
    Proof.
      intros [|] Henum; simpl in *; auto.
      destruct Henum; split; auto.
      apply Heq; auto.
    Qed.
    Hint Resolve iface_incl_wt_enum iface_incl_wt_clock : ltyping.

    Hint Constructors wt_exp : ltyping.
    Fact iface_incl_wt_exp : forall Γ e,
        wt_exp G1 Γ e ->
        wt_exp G2 Γ e.
    Proof with eauto with ltyping.
      induction e using exp_ind2; intros Hwt; inv Hwt...
      1-8:econstructor; simpl_Forall; eauto with ltyping.
      1-5:apply Heq; auto.
      - eapply Heq in H7 as (?&Hfind'&(?&?&?&?)).
        econstructor; simpl_Forall; eauto with ltyping.
        1,2:congruence.
    Qed.

    Fact iface_incl_wt_equation : forall Γ equ,
        wt_equation G1 Γ equ ->
        wt_equation G2 Γ equ.
    Proof.
      intros ? [xs es] Hwt.
      simpl in *. destruct Hwt.
      split.
      + rewrite Forall_forall in *. intros x Hin.
        eapply iface_incl_wt_exp; eauto.
      + assumption.
    Qed.

    Fact iface_incl_wt_scope {A} (P_wt1 P_wt2: _ -> _ -> Prop) : forall Γ locs (blks : A),
        (forall Γ, P_wt1 Γ blks -> P_wt2 Γ blks) ->
        wt_scope P_wt1 G1 Γ (Scope locs blks) ->
        wt_scope P_wt2 G2 Γ (Scope locs blks).
    Proof.
      intros * Hp Hwt. inv Hwt.
      econstructor; eauto.
      - unfold wt_clocks in *; simpl_Forall; eauto with ltyping.
      - simpl_Forall; eauto with ltyping.
      - simpl_Forall. destruct o as [(?&?)|]; simpl in *; auto.
        destruct_conjs; split; eauto using iface_incl_wt_exp.
    Qed.

    Fact iface_incl_wt_block : forall d Γ,
        wt_block G1 Γ d ->
        wt_block G2 Γ d.
    Proof.
      induction d using block_ind2; intros * Hwt; inv Hwt.
      - constructor; auto using iface_incl_wt_equation.
      - constructor; auto using iface_incl_wt_exp.
        rewrite Forall_forall in *; eauto.
      - econstructor; eauto using iface_incl_wt_exp.
        + apply Heq; auto.
        + simpl_Forall; eauto. destruct s.
          eapply iface_incl_wt_scope; eauto. intros; simpl_Forall; eauto.
      - econstructor; eauto; simpl_Forall; eauto using iface_incl_wt_exp, iface_incl_wt_clock.
        destruct s as [?(?&?)].
        eapply iface_incl_wt_scope; eauto.
        intros ? (?&?); split; simpl_Forall; eauto using iface_incl_wt_exp.
      - constructor.
        eapply iface_incl_wt_scope; eauto. intros; simpl_Forall; eauto.
    Qed.

  End interface_incl.

  Fact iface_incl_wt_node {PSyn prefs} (G1 G2: @global PSyn prefs) : forall n,
      global_iface_incl G1 G2 ->
      wt_node G1 n ->
      wt_node G2 n.
  Proof.
    intros * Hincl Hwt.
    destruct Hwt as (Hwt1&Hwt2&Hwt3&Hwt4).
    repeat split.
    1-3:unfold wt_clocks in *; simpl_Forall; eauto using iface_incl_wt_clock, iface_incl_wt_enum.
    eauto using iface_incl_wt_block.
  Qed.

  Global Hint Resolve iface_incl_wt_enum iface_incl_wt_clock
         iface_incl_wt_exp iface_incl_wt_equation iface_incl_wt_block : ltyping.

  (** *** wt implies wl *)

  Local Hint Constructors wl_exp wl_block : ltyping.

  Fact wt_exp_wl_exp {PSyn prefs} : forall (G: @global PSyn prefs) Γ e,
      wt_exp G Γ e ->
      wl_exp G e.
  Proof with eauto.
    induction e using exp_ind2; intro Hwt; inv Hwt; simpl in *; auto with ltyping.
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
  Global Hint Resolve wt_exp_wl_exp : ltyping.

  Corollary Forall_wt_exp_wl_exp {PSyn prefs} : forall (G: @global PSyn prefs) Γ es,
      Forall (wt_exp G Γ) es ->
      Forall (wl_exp G) es.
  Proof. intros. rewrite Forall_forall in *; eauto with ltyping. Qed.
  Global Hint Resolve Forall_wt_exp_wl_exp : ltyping.

  Fact wt_equation_wl_equation {PSyn prefs} : forall (G: @global PSyn prefs) Γ equ,
      wt_equation G Γ equ ->
      wl_equation G equ.
  Proof with eauto with ltyping.
    intros ?? [xs es] Hwt.
    inv Hwt. constructor.
    + rewrite Forall_forall in *...
    + apply Forall2_length in H0.
      rewrite typesof_annots, map_length in H0...
  Qed.
  Global Hint Resolve wt_equation_wl_equation : ltyping.

  Fact wt_scope_wl_scope {A} (P_wt: _ -> _ -> Prop) (P_wl: _ -> Prop) {PSyn prefs} (G: @global PSyn prefs) :
    forall locs (blks: A) Γ,
      (forall Γ, P_wt Γ blks -> P_wl blks) ->
      wt_scope P_wt G Γ (Scope locs blks) ->
      wl_scope P_wl G (Scope locs blks).
  Proof.
    intros * Hp Hwt. inv Hwt.
    constructor; eauto.
    simpl_Forall. destruct o as [(?&?)|]; simpl in *; auto; destruct_conjs.
    split; eauto with ltyping.
    rewrite <-length_typeof_numstreams, H1; auto.
  Qed.

  Fact wt_block_wl_block {PSyn prefs} : forall (G: @global PSyn prefs) d Γ,
      wt_block G Γ d ->
      wl_block G d.
  Proof.
    induction d using block_ind2; intros * Wt; inv Wt; eauto with ltyping.
    - econstructor; eauto with ltyping.
      + eapply Forall_Forall in H; eauto. clear H2.
        eapply Forall_impl; [|eauto]. intros ? (?&?); eauto with ltyping.
      + now rewrite <-length_typeof_numstreams, H5.
    - econstructor; eauto with ltyping.
      + rewrite <-length_typeof_numstreams, H3; auto.
      + simpl_Forall; eauto.
        destruct s. eapply wt_scope_wl_scope; eauto. intros; simpl_Forall; eauto.
    - econstructor; simpl_Forall; eauto.
      + split; eauto with ltyping. now rewrite <-length_typeof_numstreams, H2.
      + destruct s as [?(?&?)]. eapply wt_scope_wl_scope; eauto.
        intros * (?&?); split; simpl_Forall; eauto.
        split; eauto with ltyping. now rewrite <-length_typeof_numstreams, H10.
    - constructor. eapply wt_scope_wl_scope; eauto.
      intros; simpl_Forall; eauto.
  Qed.
  Global Hint Resolve wt_block_wl_block : ltyping.

  Fact wt_node_wl_node {PSyn prefs} : forall (G: @global PSyn prefs) n,
      wt_node G n ->
      wl_node G n.
  Proof with eauto with ltyping.
    intros G n [_ [_ [_ Hwt]]].
    unfold wl_node...
  Qed.
  Global Hint Resolve wt_node_wl_node : ltyping.

  Fact wt_global_wl_global {PSyn prefs} : forall (G: @global PSyn prefs),
      wt_global G ->
      wl_global G.
  Proof with eauto with ltyping.
    intros G (_&Hwt).
    unfold wl_global, wt_program in *.
    induction Hwt; constructor...
    destruct H...
  Qed.
  Global Hint Resolve wt_global_wl_global : ltyping.

  (** *** If an expression is well-typed, all the enums appearing inside are well-typed *)
  Section wt_enum.
    Context {PSyn : block -> Prop}.
    Context {prefs : PS.t}.
    Variable G : @global PSyn prefs.

    Hypothesis HwtG : wt_global G.

    Lemma wt_exp_wt_enum : forall Γ e,
        Forall (wt_enum G) (map (fun '(_, e) => e.(typ)) Γ) ->
        wt_exp G Γ e ->
        Forall (wt_enum G) (typeof e).
    Proof.
      induction e using exp_ind2; intros * Hvars Hwt; inv Hwt; simpl.
      - (* const *)
        repeat constructor.
      - (* enum *)
        repeat constructor; auto. lia.
      - (* var *)
        repeat constructor. inv H1. simpl_Forall; auto.
      - (* last *)
        repeat constructor. inv H1. simpl_Forall; auto.
      - (* unop *) constructor; auto.
      - (* binop *) constructor; auto.
      - (* fby *)
        rewrite <-H7. unfold typesof.
        rewrite flat_map_concat_map, Forall_concat, Forall_map.
        rewrite Forall_forall in H4, H. eapply Forall_forall; eauto.
      - (* arrow *)
        rewrite <-H7. unfold typesof.
        rewrite flat_map_concat_map, Forall_concat, Forall_map.
        rewrite Forall_forall in H4, H. eapply Forall_forall; eauto.
      - (* when *)
        unfold typesof.
        rewrite flat_map_concat_map, Forall_concat, Forall_map.
        rewrite Forall_forall in H7, H. eapply Forall_forall; eauto.
      - (* merge *)
        inv H; try solve [exfalso; eauto]. inv H7. inv H8.
        unfold typesof.
        rewrite flat_map_concat_map, Forall_concat, Forall_map.
        rewrite Forall_forall in H10, H0. eapply Forall_forall; eauto.
      - (* case *)
        inv H11; try congruence.
        unfold typesof.
        rewrite flat_map_concat_map, Forall_concat, Forall_map.
        inv H. inv H10. rewrite Forall_forall in *; intros. eapply H4; eauto.
        eapply Forall_forall; eauto.
      - (* case (default) *)
        simpl in *.
        unfold typesof.
        rewrite flat_map_concat_map, Forall_concat, Forall_map.
        eapply Forall_impl_In; [|eapply H0]; intros.
        eapply H2; eauto. rewrite Forall_forall in *; eauto.
      - (* app *)
        eapply wt_find_node in H7 as (?&Hwtn&Heq); eauto.
        destruct Hwtn as (_&_&Henums&_).
        unfold idty in Henums. repeat rewrite Forall_map in Henums.
        repeat rewrite Forall_app in Henums. destruct Henums as (_&Henums).
        eapply Forall2_ignore2 in H9. simpl_Forall. subst.
        destruct t0; simpl in *; auto.
        rewrite <-Heq; auto.
    Qed.

    Corollary wt_exps_wt_enum : forall Γ es,
        Forall (wt_enum G) (map (fun '(_, e) => e.(typ)) Γ) ->
        Forall (wt_exp G Γ) es ->
        Forall (wt_enum G) (typesof es).
    Proof.
      unfold typesof; induction es;
        intros * Hen1 Hwt; inv Hwt; simpl; auto.
      apply Forall_app; split; auto.
      eapply wt_exp_wt_enum in H1; eauto.
    Qed.

  End wt_enum.

  (** ** wc implies wx *)

  Global Hint Constructors wx_exp wl_block : ltyping.

  Lemma wt_clock_wx_clock : forall enums vars ck,
      wt_clock enums vars ck ->
      wx_clock vars ck.
  Proof.
    induction ck; intros * Hwt; inv Hwt; constructor; eauto.
    inv H2. econstructor; eauto using In_InMembers.
  Qed.

  Fact wt_exp_wx_exp {PSyn prefs} (G: @global PSyn prefs) : forall Γ e,
      wt_exp G Γ e ->
      wx_exp Γ e.
  Proof with eauto with ltyping senv.
    induction e using exp_ind2; intro Hwt; inv Hwt...
    - (* fby *)
      constructor; simpl_Forall...
    - (* arrow *)
      constructor; simpl_Forall...
    - (* when *)
      constructor; simpl_Forall...
    - (* merge *)
      constructor...
      simpl_Forall...
    - (* case *)
      constructor...
      + simpl_Forall...
      + intros ? Heq. inv Heq.
   - (* case *)
      constructor...
      + simpl_Forall...
      + intros ? Heq. inv Heq. simpl in *.
        simpl_Forall...
    - (* app *)
      econstructor... 1,2:simpl_Forall...
  Qed.
  Global Hint Resolve wt_clock_wx_clock wt_exp_wx_exp : ltyping.

  Corollary Forall_wt_exp_wx_exp {PSyn prefs} (G: @global PSyn prefs) : forall Γ es,
      Forall (wt_exp G Γ) es ->
      Forall (wx_exp Γ) es.
  Proof. intros. rewrite Forall_forall in *; eauto with ltyping. Qed.
  Global Hint Resolve Forall_wt_exp_wx_exp : ltyping.

  Fact wt_equation_wx_equation {PSyn prefs} (G: @global PSyn prefs) : forall Γ equ,
      wt_equation G Γ equ ->
      wx_equation Γ equ.
  Proof with eauto with ltyping.
    intros ? [xs es] (Hwt1&Hwt2).
    constructor.
    + rewrite Forall_forall in *...
    + apply Forall2_ignore2 in Hwt2. simpl_Forall; eauto with senv.
  Qed.
  Global Hint Resolve wt_equation_wx_equation : ltyping.

  Fact wt_scope_wx_scope {A} (P_wt: _ -> _ -> Prop) (P_wx: _ -> _ -> Prop) {PSyn prefs} (G: @global PSyn prefs) :
    forall locs (blks: A) Γ,
      (forall Γ, P_wt Γ blks -> P_wx Γ blks) ->
      wt_scope P_wt G Γ (Scope locs blks) ->
      wx_scope P_wx Γ (Scope locs blks).
  Proof.
    intros * Hp Hwt. inv Hwt.
    econstructor; eauto.
    simpl_Forall. destruct o as [(?&?)|]; simpl in *; auto; destruct_conjs.
    eauto with ltyping.
  Qed.

  Fact wt_block_wx_block {PSyn prefs} (G: @global PSyn prefs) : forall blk Γ,
      wt_block G Γ blk ->
      wx_block Γ blk.
  Proof.
    induction blk using block_ind2; intros * Wt; inv Wt; eauto with ltyping.
    1-5:econstructor; simpl_Forall; eauto with ltyping.
    - destruct s. eapply wt_scope_wx_scope; eauto.
      intros; simpl_Forall; eauto.
    - destruct s as [?(?&?)].
      eapply wt_scope_wx_scope; eauto.
      intros * (?&?); split; simpl_Forall; eauto with ltyping.
    - eapply wt_scope_wx_scope; eauto.
      intros; simpl_Forall; eauto with ltyping.
  Qed.
  Global Hint Resolve wt_block_wx_block : ltyping.

  Fact wt_node_wx_node {PSyn prefs} : forall (G: @global PSyn prefs) n,
      wt_node G n ->
      wx_node n.
  Proof.
    intros G n (_&_&_&Hwt).
    unfold wx_node.
    eapply wt_block_wx_block in Hwt; auto.
  Qed.
  Global Hint Resolve wt_node_wx_node : ltyping.

  Fact wt_global_wx_global {PSyn prefs} : forall (G: @global PSyn prefs),
      wt_global G ->
      wx_global G.
  Proof with eauto with ltyping.
    intros G (?&Hwt).
    unfold wt_global, wx_global, wt_program, units in *; simpl in *.
    induction Hwt...
    destruct H0...
  Qed.
  Global Hint Resolve wt_global_wx_global : ltyping.

  (** Other useful stuff *)

  Lemma wt_clock_Is_free_in : forall x enums env ck,
      wt_clock enums env ck ->
      Is_free_in_clock x ck ->
      InMembers x env.
  Proof.
    induction ck; intros Hwt Hfree;
      inv Hwt; inv Hfree; inv H2; eauto using In_InMembers.
  Qed.

End LTYPING.

Module LTypingFun
       (Ids   : IDS)
       (Op    : OPERATORS)
       (OpAux : OPERATORS_AUX Ids Op)
       (Cks   : CLOCKS Ids Op OpAux)
       (Senv  : STATICENV Ids Op OpAux Cks)
       (Syn   : LSYNTAX Ids Op OpAux Cks Senv)
       <: LTYPING Ids Op OpAux Cks Senv Syn.
  Include LTYPING Ids Op OpAux Cks Senv Syn.
End LTypingFun.
