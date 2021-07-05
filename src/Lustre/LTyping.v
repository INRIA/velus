From Velus Require Import Common.
From Velus Require Import CommonProgram.
From Velus Require Import CommonTyping.
From Velus Require Import Operators.
From Velus Require Import Clocks.
From Velus Require Import Lustre.LSyntax.

From Coq Require Import List.
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

  (** ** Expressions and equations *)
  Section WellTyped.
    Context {prefs : PS.t}.

    Variable G     : @global prefs.
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
        snd tn = length es ->
        es <> nil ->
        Forall (Forall wt_exp) es ->
        Forall (fun es => typesof es = tys) es ->
        wt_nclock G.(enums) Γ nck ->
        wt_exp (Emerge (x, Tenum tn) es (tys, nck))

    | wt_Ecase: forall e brs d tn tys nck,
        wt_exp e ->
        typeof e = [Tenum tn] ->
        In tn G.(enums) ->
        snd tn = length brs ->
        brs <> nil ->
        (forall es, In (Some es) brs -> Forall wt_exp es) ->
        (forall es, In (Some es) brs -> typesof es = tys) ->
        Forall wt_exp d ->
        typesof d = tys ->
        wt_nclock G.(enums) Γ nck ->
        wt_exp (Ecase e brs d (tys, nck))

    | wt_Eapp: forall f es er anns n,
        Forall wt_exp es ->
        Forall wt_exp er ->
        find_node f G = Some n ->
        Forall2 (fun et '(_, (t, _)) => et = t) (typesof es) n.(n_in) ->
        Forall2 (fun a '(_, (t, _)) => fst a = t) anns n.(n_out) ->
        Forall (fun e => typeof e = [bool_velus_type]) er ->
        Forall (fun a => wt_nclock G.(enums) (Γ++(idty (fresh_ins es++anon_streams anns))) (snd a)) anns ->
        wt_exp (Eapp f es er anns).

    Definition wt_equation (eq : equation) : Prop :=
      let (xs, es) := eq in
      Forall wt_exp es
      /\ Forall2 (fun x ty=> In (x, ty) Γ) xs (typesof es).

    Inductive wt_block : block -> Prop :=
    | wt_Beq: forall eq,
        wt_equation eq ->
        wt_block (Beq eq)
    | wt_Breset: forall blocks er,
        Forall wt_block blocks ->
        wt_exp er ->
        typeof er = [bool_velus_type] ->
        wt_block (Breset blocks er).

  End WellTyped.

  Definition wt_clocks enums (Γ : list (ident * (type * clock))) : list (ident * (type * clock)) -> Prop :=
    Forall (fun '(_, (_, ck)) => wt_clock enums (idty Γ) ck).

  Definition wt_node {prefs} (G: @global prefs) (n: @node prefs) : Prop
    :=    wt_clocks G.(enums) n.(n_in) n.(n_in)
       /\ wt_clocks G.(enums) (n.(n_in) ++ n.(n_out)) n.(n_out)
       /\ wt_clocks G.(enums) (n.(n_in) ++ n.(n_out) ++ n.(n_vars)) n.(n_vars)
       /\ Forall (wt_enum G) (map snd (idty (n.(n_in) ++ n.(n_vars) ++ n.(n_out))))
       /\ Forall (wt_block G (idty (n.(n_in) ++ n.(n_vars) ++ n.(n_out)))) n.(n_blocks).

  Definition wt_global {prefs} (G: @global prefs) : Prop :=
    In (bool_id, 2) G.(enums) /\
    wt_program wt_node G.

  Hint Constructors wt_clock wt_nclock wt_exp wt_block : ltyping.
  Hint Unfold wt_equation : ltyping.

  Section wt_exp_ind2.
    Context (prefs : PS.t).

    Variable (G : @global prefs).
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
        snd tn = length es ->
        es <> nil ->
        Forall (Forall (wt_exp G Γ)) es ->
        Forall (Forall P) es ->
        Forall (fun es => typesof es = tys) es ->
        wt_nclock G.(enums) Γ nck ->
        P (Emerge (x, Tenum tn) es (tys, nck)).

    Hypothesis EcaseCase:
      forall e brs d tn tys nck,
        wt_exp G Γ e ->
        P e ->
        typeof e = [Tenum tn] ->
        In tn G.(enums) ->
        snd tn = length brs ->
        brs <> nil ->
        (forall es, In (Some es) brs -> Forall (wt_exp G Γ) es) ->
        (forall es, In (Some es) brs -> Forall P es) ->
        (forall es, In (Some es) brs -> typesof es = tys) ->
        Forall (wt_exp G Γ) d ->
        Forall P d ->
        typesof d = tys ->
        wt_nclock G.(enums) Γ nck ->
        P (Ecase e brs d (tys, nck)).

    Hypothesis EappCase:
      forall f es er anns n,
        Forall (wt_exp G Γ) es ->
        Forall (wt_exp G Γ) er ->
        Forall P es ->
        Forall P er ->
        find_node f G = Some n ->
        Forall2 (fun et '(_, (t, _)) => et = t) (typesof es) n.(n_in) ->
        Forall2 (fun a '(_, (t, _)) => fst a = t) anns n.(n_out) ->
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
      - eapply EcaseCase; eauto.
        + clear H2 H3 H5.
          intros ? Hin. specialize (H4 _ Hin). clear Hin.
          induction H4; constructor; auto.
        + clear H7.
          induction H6; constructor; auto.
      - eapply EappCase; eauto.
        + clear H2 H5. induction H; eauto.
        + clear H4. induction H0; eauto.
    Qed.

  End wt_exp_ind2.

  Lemma wt_global_NoDup {prefs}:
    forall (g : @global prefs),
      wt_global g ->
      NoDup (map name (nodes g)).
  Proof.
    intros * (?&Wt).
    eapply wt_program_NoDup in Wt; eauto.
  Qed.

  Lemma wt_find_node {prefs}:
    forall (G : @global prefs) f n,
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

  Instance wt_exp_Proper {prefs}:
    Proper (@eq (@global prefs) ==> @Permutation.Permutation (ident * type)
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

  Instance wt_exp_pointwise_Proper {prefs}:
    Proper (@eq (@global prefs) ==> @Permutation.Permutation (ident * type)
                                     ==> pointwise_relation exp iff) wt_exp.
  Proof.
    intros G G' HG env' env Henv e.
    now rewrite HG, Henv.
  Qed.

  Instance wt_equation_Proper {prefs}:
    Proper (@eq (@global prefs) ==> @Permutation.Permutation (ident * type)
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

    Lemma wt_exp_incl {prefs} : forall (G: @global prefs) vars vars' e,
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

    Lemma wt_equation_incl {prefs} : forall (G: @global prefs) vars vars' eq,
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

    Lemma wt_block_incl {prefs} : forall (G: @global prefs) vars vars' d,
        incl vars vars' ->
        wt_block G vars d ->
        wt_block G vars' d .
    Proof.
      induction d using block_ind2; intros * Incl Wt; inv Wt.
      - constructor. eauto using wt_equation_incl.
      - econstructor; eauto using wt_exp_incl.
        eapply Forall_Forall in H; eauto. clear H2.
        eapply Forall_impl; [|eauto]; intros ? (?&?); eauto.
    Qed.

  End incl.

  Local Hint Resolve wt_clock_incl incl_appl incl_refl.
  Lemma wt_exp_clockof {prefs}:
    forall (G: @global prefs) env e,
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

  Section ValidateExpression.
    Context {prefs : PS.t}.

    Variable G : @global prefs.
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

      | Emerge (x, Tenum (xt, n)) brs (tys, nck) =>
        do tss <- omap (fun es => oconcat (map check_exp es)) brs;
        if check_var x (Tenum (xt, n)) && check_enum (Tenum (xt, n))
           && (length brs ==b n) && (length brs <>b 0)
           && (forallb (fun ts => forall2b equiv_decb ts tys) tss)
           && (check_nclock eenv venv nck)
        then Some tys else None

      | Ecase e brs d (tys, nck) =>
        do tss <- omap (or_default_with (Some tys) (fun es => oconcat (map check_exp es))) brs;
        do tds <- oconcat (map check_exp d);
        do xt <- assert_singleton (check_exp e);
        match xt with
        | Tenum (xt, n) =>
          if check_enum (Tenum (xt, n))
             && (length brs ==b n) && (length brs <>b 0)
             && (forallb (fun ts => (forall2b equiv_decb ts tys)) (tds::tss))
             && (check_nclock eenv venv nck)
          then Some tys else None
        | _ => None
        end

      | Eapp f es er anns =>
        do n <- find_node f G;
        do ts <- oconcat (map check_exp es);
        do tr <- omap check_exp er;
        if (forall2b (fun et '(_, (t, _)) => et ==b t) ts n.(n_in))
             && (forall2b (fun '(ot, oc) '(_, (t, _)) =>
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
        if (forall2b (fun et '(_, (t, _)) => et ==b t) ts n.(n_in))
             && (forall2b (fun '(ot, oc) '(_, (t, _)) =>
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

    Fixpoint check_block (d : block) : bool :=
      match d with
      | Beq eq => check_equation eq
      | Breset blocks er =>
        forallb check_block blocks &&
        match check_exp er with
        | Some [tyr] => tyr ==b bool_velus_type
        | _ => false
        end
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
      forall {f} ess tys,
        (forall es e tys,
            In es ess ->
            In e es ->
            NoDupMembers (Env.elements venv++idty (fresh_in e)) ->
            f e = Some tys ->
            wt_exp G (Env.elements venv) e /\ typeof e = tys) ->
        NoDupMembers (Env.elements venv++idty (flat_map fresh_ins ess)) ->
        omap (fun es => oconcat (map f es)) ess = Some tys ->
        Forall (Forall (wt_exp G (Env.elements venv))) ess
        /\ Forall2 (fun es tys => typesof es = tys) ess tys.
    Proof.
      induction ess as [|es ess IH]; intros tys WTf ND CE. now inv CE; auto.
      simpl in CE. destruct (oconcat (map f es)) eqn:Ce; [|now omonadInv CE].
      eapply oconcat_map_check_exp' in Ce as (?&?); eauto with datatypes.
      destruct (omap _ _) as [tes|]; [|now omonadInv CE].
      omonadInv CE. simpl.
      specialize (IH tes) as (? & ?); eauto using in_cons.
      + unfold fresh_ins, idty in *; simpl in *. rewrite map_app in *.
        rewrite Permutation_swap in ND. apply NoDupMembers_app_r in ND; auto.
      + unfold fresh_ins, idty in *; simpl in *. rewrite map_app in *.
        rewrite app_assoc in ND. apply NoDupMembers_app_l in ND; auto.
    Qed.

    Lemma omap_concat_map_check_exp'':
      forall {f} ess dty tys,
        (forall es e tys,
            In (Some es) ess ->
            In e es ->
            NoDupMembers (Env.elements venv++idty (fresh_in e)) ->
            f e = Some tys ->
            wt_exp G (Env.elements venv) e /\ typeof e = tys) ->
        NoDupMembers (Env.elements venv++idty (flat_map (or_default_with [] fresh_ins) ess)) ->
        omap (or_default_with (Some dty) (fun es => oconcat (map f es))) ess = Some tys ->
        Forall (LiftO True (Forall (wt_exp G (Env.elements venv)))) ess
        /\ Forall2 (fun es tys => LiftO True (fun es => typesof es = tys) es) ess tys.
    Proof.
      induction ess as [|es ess IH]; intros * WTf ND CE. now inv CE; auto.
      simpl in CE.
      destruct es; simpl in *.
      - destruct (oconcat (map _ l)) eqn:Ce; [|now omonadInv CE].
        destruct (omap _ _) as [tes|] eqn:CE''; [|now omonadInv CE].
        omonadInv CE. simpl.
        eapply oconcat_map_check_exp' in Ce as (?&?); eauto with datatypes.
        specialize (IH dty tes) as (? & ?); eauto using in_cons.
        + unfold fresh_ins, idty in *; simpl in *. rewrite map_app in *.
          rewrite Permutation_swap in ND. apply NoDupMembers_app_r in ND; auto.
        + unfold fresh_ins, idty in *; simpl in *. rewrite map_app in *.
          rewrite app_assoc in ND. apply NoDupMembers_app_l in ND; auto.
      - destruct (omap _ _) as [tes|] eqn:CE'; [|now omonadInv CE].
        omonadInv CE. simpl.
        specialize (IH dty tes) as (? & ?); eauto using in_cons.
        split; constructor; simpl; auto.
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
            NoDupMembers (Env.elements venv++idty (fresh_in e)) ->
            f e = Some tys ->
            wt_exp G (Env.elements venv) e /\ typeof e = tys) ->
        NoDupMembers (Env.elements venv++idty (fresh_ins es)) ->
        omap f es = Some tys ->
        Forall (wt_exp G (Env.elements venv)) es
        /\ Forall2 (fun e ty => typeof e = ty) es tys.
    Proof.
      induction es as [|e es IH]; intros tys WTf ND CE. now inv CE; auto.
      simpl in CE. destruct (f e) eqn:Ce; [|now omonadInv CE].
      destruct (omap f es) as [tes|]; [|now omonadInv CE].
      omonadInv CE. simpl.
      apply WTf in Ce as (Ce1 & ?); auto with datatypes.
      destruct (IH tes) as (? & ?); auto.
      intros * Ies ND' Fe. apply WTf in Fe; auto with datatypes.
      + unfold fresh_ins, idty in *; simpl in *. rewrite map_app in *.
        rewrite Permutation_swap in ND. apply NoDupMembers_app_r in ND; auto.
      + unfold fresh_ins, idty in *; simpl in *. rewrite map_app in *.
        rewrite app_assoc in ND. apply NoDupMembers_app_l in ND; auto.
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
      induction e using exp_ind2; simpl; intros tys ND CE;
      repeat progress
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

      Ltac ndup_simpl :=
        unfold idty in *; repeat rewrite map_app in *.
      Ltac ndup_l H :=
        ndup_simpl;
        rewrite app_assoc in H; apply NoDupMembers_app_l in H; auto.
      Ltac ndup_r H :=
        ndup_simpl;
        rewrite Permutation_swap in H;
        apply NoDupMembers_app_r in H ; auto.

      - (* Eenum *)
        eapply check_enum_correct' in H as (?&?)...
      - (* Eunop *)
        apply IHe in OE0 as (? & ?)...
      - (* Ebinop *)
        assert (NoDupMembers (Env.elements venv ++ idty (fresh_in e1))) as ND1 by ndup_l ND.
        assert (NoDupMembers (Env.elements venv ++ idty (fresh_in e2))) as ND2 by ndup_r ND.
        apply IHe1 in OE0 as (? & ?); apply IHe2 in OE1 as (? & ?)...
      - (* Efby *)
        take (Forall _ e0s) and rewrite Forall_forall in it.
        take (Forall _ es) and rewrite Forall_forall in it.
        apply oconcat_map_check_exp' in OE0 as (? & ?)...
        2:ndup_l ND.
        apply oconcat_map_check_exp' in OE1 as (? & ?)...
        2:ndup_r ND.
        repeat constructor; eauto. 1,2:congruence.
      - (* Earrow *)
        take (Forall _ e0s) and rewrite Forall_forall in it.
        take (Forall _ es) and rewrite Forall_forall in it.
        apply oconcat_map_check_exp' in OE0 as (? & ?)...
        2:ndup_l ND.
        apply oconcat_map_check_exp' in OE1 as (? & ?)...
        2:ndup_r ND.
        repeat constructor; eauto. 1,2:congruence.
      - (* Ewhen *)
        subst. take (Forall _ es) and rewrite Forall_forall in it.
        take (oconcat (map check_exp _) = Some _) and
             apply oconcat_map_check_exp' in it as (? & ?)...
        eapply check_enum_correct' in H0 as (?&?)...
      - (* Emerge *)
        take (Forall _ es) and (repeat setoid_rewrite Forall_forall in it).
        take (omap _ _ = Some _) and
             apply omap_concat_map_check_exp' in it as (? & ?); eauto.
        assert (Forall (fun es => typesof es = tys) es); eauto.
        { clear - H2 H4. induction H4; inv H2; constructor; auto.
          apply Forall2_eq; auto. }
        apply check_enum_correct' in H5 as (?&?).
        econstructor; eauto. econstructor; eauto.
        contradict H3; subst; simpl.
        apply Bool.not_true_iff_false, nequiv_decb_false, equiv_decb_equiv. constructor.
      - (* Ecase *)
        rename es into brs; subst.
        take (check_exp _ = Some _) and apply IHe in it as (? & ?). 2:repeat ndup_l ND.
        take (Forall _ d) and (repeat setoid_rewrite Forall_forall in it).
        eapply oconcat_map_check_exp' in OE1 as (? & ?)...
        2:{ ndup_simpl. rewrite (Permutation_swap (Env.elements _)) in ND.
            apply NoDupMembers_app_r in ND. ndup_r ND. }
        take (Forall _ brs) and (repeat setoid_rewrite Forall_forall in it).
        take (omap _ _ = Some _) and
             apply omap_concat_map_check_exp'' in it as (? & ?); eauto.
        assert (forall es, In (Some es) brs -> typesof es = tys); eauto.
        { clear - H4 H8. eapply Forall2_ignore2 in H8.
          intros ? Hin. rewrite Forall_forall in *.
          specialize (H8 _ Hin) as (?&Hin'&Hty); simpl in *. rewrite Hty.
          specialize (H4 _ Hin') as Heq.
          apply Forall2_eq; auto. }
        + apply check_enum_correct' in H1 as (?&?).
          econstructor; eauto. econstructor; eauto.
          * contradict H5; subst; simpl.
            apply Bool.not_true_iff_false, nequiv_decb_false, equiv_decb_equiv. constructor.
          * intros ? Hin. eapply Forall_forall in H; eauto.
            simpl in H; auto.
        + intros * Hin ???. specialize (it1 _ Hin). simpl in it1.
          eapply Forall_forall in it1; eauto.
        + ndup_simpl.
          rewrite (Permutation_swap (Env.elements _)) in ND.
          apply NoDupMembers_app_r in ND.
          ndup_l ND.
      - (* Eapp *)
        take (Forall _ es) and rewrite Forall_forall in it.
        take (Forall _ er) and rewrite Forall_forall in it.
        take (oconcat (map check_exp _) = Some _) and
             apply oconcat_map_check_exp' in it as (? & ?); auto.
        2: { ndup_simpl.
             rewrite app_assoc in ND.
             apply NoDupMembers_app_l in ND.
             assumption. }
        take (omap check_exp _ = Some _) and
             apply omap_check_exp' in it as (? & ?); auto.
        2: { ndup_simpl.
             rewrite Permutation_swap, app_assoc in ND.
             apply NoDupMembers_app_l in ND.
             assumption. }
        split; auto. subst.
        assert (Forall2 (fun et '(_, (t, _)) => et = t) (typesof es) n.(n_in)).
        { take (Forall2 _ (typesof es) n.(n_in))
               and apply Forall2_impl_In with (2:=it).
          intros ? (? & (? & ?)) ? ? EQ.
          now rewrite equiv_decb_equiv in EQ. }
        assert (Forall2 (fun ann '(_, (t, _)) => fst ann = t) a n.(n_out)).
        { take (Forall2 _ _ n.(n_out)) and apply Forall2_impl_In with (2:=it).
          intros (? & ?) (? & (? & ?)) ? ? EQ.
          apply Bool.andb_true_iff in EQ as (EQ1 & EQ2).
          now rewrite equiv_decb_equiv in EQ2. }
        assert (Forall (fun ann => wt_nclock G.(enums) ((Env.elements venv)++idty (fresh_ins es++anon_streams a)) (snd ann)) a).
        { repeat take (Forall2 _ _ n.(n_out)) and apply Forall2_ignore2 in it.
          apply Forall_impl_In with (2:=it).
          intros (? & ?) ? ((? & (? & ?)) & (? & EQ)); simpl.
          apply Bool.andb_true_iff in EQ as (EQ1 & EQ2).
          apply check_nclock_correct in EQ1. rewrite Henums, Env.elements_adds in EQ1; auto.
          ndup_simpl.
          rewrite app_assoc in ND.
          rewrite Permutation_app_comm in ND.
          rewrite <- app_assoc in ND. apply NoDupMembers_app_r in ND.
          rewrite Permutation_app_comm in ND.
          rewrite <- app_assoc in ND; auto.
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
           apply oconcat_map_check_exp in it as (? & ?); auto.
      2: { ndup_simpl...
           rewrite app_assoc in ND.
           apply NoDupMembers_app_l in ND... }
      take (omap check_exp _ = Some _) and
             apply omap_check_exp in it as (? & ?); auto.
        2: { ndup_simpl.
             rewrite Permutation_swap in ND.
             apply NoDupMembers_app_r in ND... }
      subst.
      assert (Forall2 (fun et '(_, (t, _)) => et = t) (typesof l) n.(n_in)).
        { take (Forall2 _ (typesof l) n.(n_in))
               and apply Forall2_impl_In with (2:=it).
          intros ? (? & (? & ?)) ? ? EQ.
          now rewrite equiv_decb_equiv in EQ. }
        assert (Forall2 (fun ann '(_, (t, _)) => fst ann = t) l1 n.(n_out)).
        { take (Forall2 _ _ n.(n_out)) and apply Forall2_impl_In with (2:=it).
          intros (? & ?) (? & (? & ?)) ? ? EQ.
          apply Bool.andb_true_iff in EQ as (EQ1 & EQ2).
          now rewrite equiv_decb_equiv in EQ2. }
        assert (Forall (fun a => wt_nclock G.(enums) (Env.elements venv ++ idty (fresh_ins l++anon_streams l1)) (snd a)) l1).
        { repeat take (Forall2 _ _ n.(n_out)) and apply Forall2_ignore2 in it.
          apply Forall_impl_In with (2:=it).
          intros (? & ?) ? ((? & (? & ?)) & (? & EQ)); simpl.
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

    Lemma check_block_correct : forall d,
        NoDupMembers (Env.elements venv++(idty (anon_in_block d))) ->
        check_block d = true ->
        wt_block G (Env.elements venv) d.
    Proof.
      induction d using block_ind2; intros * ND CD; simpl in *.
      - eapply check_equation_correct in CD; eauto.
      - eapply Bool.andb_true_iff in CD as (CDs&CE).
        eapply forallb_Forall in CDs.
        destruct check_exp eqn:CE'; try congruence.
        eapply check_exp_correct in CE' as (Wte&Tye). 2:ndup_r ND.
        econstructor; eauto.
        + ndup_l ND. clear - H ND CDs.
          eapply Forall_Forall in H; eauto. clear CDs.
          induction H as [|?? (?&?)]; simpl in *; constructor; auto.
          * now ndup_l ND.
          * now ndup_r ND.
        + cases.
          rewrite equiv_decb_equiv in CE; inv CE.
          assumption.
    Qed.

  End ValidateExpression.

  Section ValidateGlobal.
    Definition check_node {prefs} (G : @global prefs) eenv (n : @node prefs) :=
      forallb (check_clock eenv (Env.from_list (idty (n_in n)))) (List.map (fun '(_, (_, ck)) => ck) (n_in n)) &&
      forallb (check_clock eenv (Env.from_list (idty (n_in n ++ n_out n)))) (List.map (fun '(_, (_, ck)) => ck) (n_out n)) &&
      forallb (check_clock eenv (Env.from_list (idty (n_in n ++ n_out n ++ n_vars n)))) (List.map (fun '(_, (_, ck)) => ck) (n_vars n)) &&
      forallb (check_enum eenv) (map snd (idty (n_in n ++ n_vars n ++ n_out n))) &&
      forallb (check_block G eenv (Env.from_list (idty (n_in n ++ n_vars n ++ n_out n)))) (n_blocks n).

    Definition check_global {prefs} (G : @global prefs) :=
      let eenv := Env.from_list G.(enums) in
      check_enum eenv (Tenum (bool_id, 2)) &&
      check_nodup (List.map n_name G.(nodes)) &&
      (fix aux nds := match nds with
                    | [] => true
                    | hd::tl => check_node (update G tl) eenv hd && aux tl
                    end) G.(nodes).

    Lemma check_node_correct {prefs} : forall (G: @global prefs) eenv n,
        incl (Env.elements eenv) G.(enums) ->
        check_node G eenv n = true ->
        wt_node G n.
    Proof.
      intros * Hincl Hcheck.
      specialize (n_nodup n) as Hndup.
      unfold check_node in Hcheck.
      repeat rewrite Bool.andb_true_iff in Hcheck. destruct Hcheck as [[[[Hc1 Hc2] Hc3] Hc4] Hc5].
      rewrite forallb_Forall, Forall_map in Hc1, Hc2, Hc3.
      rewrite forallb_Forall in Hc4. rewrite forallb_Forall in Hc5.
      split; [|split; [|split; [|split]]].
      1-3:(eapply Forall_impl; eauto;
           intros [_ [_ ?]] Hck;
           eapply check_clock_correct in Hck; rewrite Hincl in Hck;
           eapply wt_clock_incl; [|eauto]; eapply Env.elements_from_list_incl).
      - eapply Forall_impl; [|eauto].
        intros. eapply check_enum_correct; eauto.
      - eapply Forall_impl_In in Hc5; eauto. intros ? Hin Hwt.
        eapply check_block_correct in Hwt; auto.
        + eapply wt_block_incl; [|eauto]. eapply Env.elements_from_list_incl.
        + apply NoDupMembers_app.
          * apply Env.NoDupMembers_elements.
          * rewrite NoDupMembers_idty.
            repeat apply NoDupMembers_app_r in Hndup.
            eapply NoDupMembers_anon_in_block; eauto.
          * intros x Hin' contra.
            rewrite <- Env.In_Members, Env.In_from_list in Hin'.
            rewrite InMembers_idty in Hin', contra.
            repeat rewrite app_assoc in Hndup. repeat rewrite app_assoc in Hin'.
            eapply NoDupMembers_app_InMembers in Hndup; eauto.
            eapply Hndup, InMembers_anon_in_block; eauto.
    Qed.

    Lemma check_global_correct {prefs} : forall (G: @global prefs),
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
    Context {prefs1 prefs2 : PS.t}.
    Variable G1 : @global prefs1.
    Variable G2 : @global prefs2.

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
      1-9:econstructor; try (destruct Heq as (Henums&_); erewrite <-Henums)...
      1-11:rewrite Forall_forall in *...
      - intros ? Hin. specialize (H7 _ Hin). specialize (H _ Hin).
        rewrite Forall_forall in *...
      - intros ? Hin. specialize (H10 _ Hin). specialize (H _ Hin); simpl in H.
        rewrite Forall_forall in *...
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

    Fact iface_eq_wt_block : forall vars d,
        wt_block G1 vars d ->
        wt_block G2 vars d.
    Proof.
      induction d using block_ind2; intros * Hwt; inv Hwt.
      - constructor; auto using iface_eq_wt_equation.
      - constructor; auto using iface_eq_wt_exp.
        rewrite Forall_forall in *; eauto.
    Qed.

  End interface_eq.

  (** *** wt implies wl *)

  Hint Constructors wl_exp wl_block.

  Fact wt_exp_wl_exp {prefs} : forall (G: @global prefs) vars e,
      wt_exp G vars e ->
      wl_exp G e.
  Proof with eauto.
    induction e using exp_ind2; intro Hwt; inv Hwt; auto.
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
      + rewrite Forall_forall in *...
      + symmetry. apply length_typesof_annots.
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

  Corollary Forall_wt_exp_wl_exp {prefs} : forall (G: @global prefs) vars es,
      Forall (wt_exp G vars) es ->
      Forall (wl_exp G) es.
  Proof. intros. rewrite Forall_forall in *; eauto. Qed.
  Hint Resolve Forall_wt_exp_wl_exp.

  Fact wt_equation_wl_equation {prefs} : forall (G: @global prefs) vars equ,
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

  Fact wt_block_wl_block {prefs} : forall (G: @global prefs) vars d,
      wt_block G vars d ->
      wl_block G d.
  Proof.
    induction d using block_ind2; intros * Wt; inv Wt; eauto.
    econstructor; eauto.
    - eapply Forall_Forall in H; eauto. clear H2.
      eapply Forall_impl; [|eauto]. intros ? (?&?); auto.
    - now rewrite <-length_typeof_numstreams, H4.
  Qed.
  Hint Resolve wt_block_wl_block.

  Fact wt_node_wl_node {prefs} : forall (G: @global prefs) n,
      wt_node G n ->
      wl_node G n.
  Proof with eauto.
    intros G n [_ [_ [_ [_ Hwt]]]].
    unfold wl_node.
    rewrite Forall_forall in *...
  Qed.
  Hint Resolve wt_node_wl_node.

  Fact wt_global_wl_global {prefs} : forall (G: @global prefs),
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
    Context {prefs : PS.t}.
    Variable G : @global prefs.

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
        inv H; try congruence. inv H7. inv H8.
        unfold typesof.
        rewrite flat_map_concat_map, <-Forall_concat, Forall_map.
        rewrite Forall_forall in H10, H0. eapply Forall_forall; eauto.
      - (* case *)
        unfold typesof.
        rewrite flat_map_concat_map, <-Forall_concat, Forall_map.
        rewrite Forall_forall in H12, H0. eapply Forall_forall; eauto.
      - (* app *)
        eapply wt_find_node in H7 as (?&Hwtn&Heq); eauto.
        destruct Hwtn as (_&_&_&Henums&_).
        unfold idty in Henums. repeat rewrite Forall_map in Henums.
        repeat rewrite Forall_app in Henums. destruct Henums as (_&_&Henums).
        rewrite Forall_map.
        eapply Forall2_ignore2 in H9.
        eapply Forall_impl; [|eapply H9]. intros (?&?) ((?&?&?)&?&?); subst.
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
