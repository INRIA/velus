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

    Variable types : list type.
    Variable Γ     : static_env.

    Inductive wt_clock : clock -> Prop :=
    | wt_Cbase:
        wt_clock Cbase
    | wt_Con: forall ck x tx tn c,
        HasType Γ x (Tenum tx tn) ->
        In (Tenum tx tn) types ->
        c < length tn ->
        wt_clock ck ->
        wt_clock (Con ck x (Tenum tx tn, c)).

  End WellTyped.

  Import Permutation.

  (** ** Expressions and equations *)
  Section WellTyped.
    Context {PSyn : list decl -> block -> Prop}.
    Context {prefs : PS.t}.

    Variable G     : @global PSyn prefs.
    Variable Γ     : static_env.

    Inductive wt_exp : exp -> Prop :=
    | wt_Econst: forall c,
        wt_exp (Econst c)

    | wt_Eenum: forall k tx tn,
        wt_type G.(types) (Tenum tx tn) ->
        k < length tn ->
        wt_exp (Eenum k (Tenum tx tn))

    | wt_Evar: forall x ty nck,
        HasType Γ x ty ->
        wt_clock G.(types) Γ nck ->
        wt_exp (Evar x (ty, nck))

    | wt_Elast: forall x ty nck,
        HasType Γ x ty ->
        IsLast Γ x ->
        wt_clock G.(types) Γ nck ->
        wt_exp (Elast x (ty, nck))

    | wt_Eunop: forall op e tye ty nck,
        wt_exp e ->
        typeof e = [tye] ->
        type_unop op tye = Some ty ->
        wt_type G.(types) ty ->
        wt_clock G.(types) Γ nck ->
        wt_exp (Eunop op e (ty, nck))

    | wt_Ebinop: forall op e1 e2 ty1 ty2 ty nck,
        wt_exp e1 ->
        wt_exp e2 ->
        typeof e1 = [ty1] ->
        typeof e2 = [ty2] ->
        type_binop op ty1 ty2 = Some ty ->
        wt_type G.(types) ty ->
        wt_clock G.(types) Γ nck ->
        wt_exp (Ebinop op e1 e2 (ty, nck))

    | wt_Eextcall: forall f es tyout ck tyins,
        Forall wt_exp es ->
        Forall2 (fun ty cty => ty = Tprimitive cty) (typesof es) tyins ->
        typesof es <> [] ->
        In (f, (tyins, tyout)) G.(externs) ->
        wt_clock G.(types) Γ ck ->
        wt_exp (Eextcall f es (tyout, ck))

    | wt_Efby: forall e0s es anns,
        Forall wt_exp e0s ->
        Forall wt_exp es ->
        typesof es = map fst anns ->
        typesof e0s = map fst anns ->
        Forall (wt_clock G.(types) Γ) (map snd anns) ->
        wt_exp (Efby e0s es anns)

    | wt_Earrow: forall e0s es anns,
        Forall wt_exp e0s ->
        Forall wt_exp es ->
        typesof es = map fst anns ->
        typesof e0s = map fst anns ->
        Forall (wt_clock G.(types) Γ) (map snd anns) ->
        wt_exp (Earrow e0s es anns)

    | wt_Ewhen: forall es x b tx tn tys nck,
        HasType Γ x (Tenum tx tn) ->
        In (Tenum tx tn) G.(types) ->
        b < length tn ->
        Forall wt_exp es ->
        typesof es = tys ->
        wt_clock G.(types) Γ nck ->
        wt_exp (Ewhen es (x, Tenum tx tn) b (tys, nck))

    | wt_Emerge: forall x tx tn es tys nck,
        HasType Γ x (Tenum tx tn) ->
        In (Tenum tx tn) G.(types) ->
        Permutation (map fst es) (seq 0 (length tn)) ->
        es <> nil ->
        Forall (fun es => Forall wt_exp (snd es)) es ->
        Forall (fun es => typesof (snd es) = tys) es ->
        wt_clock G.(types) Γ nck ->
        wt_exp (Emerge (x, Tenum tx tn) es (tys, nck))

    | wt_EcaseTotal: forall e es tx tn tys nck,
        wt_exp e ->
        typeof e = [Tenum tx tn] ->
        In (Tenum tx tn) G.(types) ->
        Permutation (map fst es) (seq 0 (length tn)) ->
        es <> nil ->
        Forall (fun es => Forall wt_exp (snd es)) es ->
        Forall (fun es => typesof (snd es) = tys) es ->
        wt_clock G.(types) Γ nck ->
        wt_exp (Ecase e es None (tys, nck))

    | wt_EcaseDefault: forall e es d tx tn tys nck,
        wt_exp e ->
        typeof e = [Tenum tx tn] ->
        In (Tenum tx tn) G.(types) ->
        incl (map fst es) (seq 0 (length tn)) ->
        NoDupMembers es ->
        es <> nil ->
        Forall (fun es => Forall wt_exp (snd es)) es ->
        Forall (fun es => typesof (snd es) = tys) es ->
        Forall wt_exp d ->
        typesof d = tys ->
        wt_clock G.(types) Γ nck ->
        wt_exp (Ecase e es (Some d) (tys, nck))

    | wt_Eapp: forall f es er anns n,
        Forall wt_exp es ->
        Forall wt_exp er ->
        find_node f G = Some n ->
        Forall2 (fun et '(_, (t, _, _)) => et = t) (typesof es) n.(n_in) ->
        Forall2 (fun a '(_, (t, _, _, _)) => fst a = t) anns n.(n_out) ->
        Forall (fun e => typeof e = [bool_velus_type]) er ->
        Forall (fun a => wt_clock G.(types) Γ (snd a)) anns ->
        wt_exp (Eapp f es er anns).

    Definition wt_equation (eq : equation) : Prop :=
      let (xs, es) := eq in
      Forall wt_exp es
      /\ Forall2 (HasType Γ) xs (typesof es).

  End WellTyped.

  Definition wt_clocks types Γ : static_env -> Prop :=
    Forall (fun '(_, ann) => wt_clock types Γ ann.(clo)).

  Inductive wt_scope {A} (P_wt : static_env -> A -> Prop) {PSyn prefs} (G: @global PSyn prefs) :
    static_env -> scope A -> Prop :=
  | wt_Scope : forall Γ locs blks,
      let Γ' := Γ ++ senv_of_decls locs in
      wt_clocks G.(types) Γ' (senv_of_decls locs) ->
      Forall (wt_type G.(types)) (map (fun '(_, (ty, _, _, _)) => ty) locs) ->
      P_wt Γ' blks ->
      wt_scope P_wt G Γ (Scope locs blks).

  Inductive wt_branch {A} (P_wt : A -> Prop) : branch A -> Prop :=
  | wt_Branch : forall caus blks,
      P_wt blks ->
      wt_branch P_wt (Branch caus blks).

  Inductive wt_block {PSyn prefs} (G: @global PSyn prefs) : static_env -> block -> Prop :=
  | wt_Beq: forall Γ eq,
      wt_equation G Γ eq ->
      wt_block G Γ (Beq eq)

  | wt_Blast: forall Γ x e ty,
      HasType Γ x ty ->
      IsLast Γ x ->
      wt_exp G Γ e ->
      typeof e = [ty] ->
      wt_block G Γ (Blast x e)

  | wt_Breset: forall Γ blocks er,
      Forall (wt_block G Γ) blocks ->
      wt_exp G Γ er ->
      typeof er = [bool_velus_type] ->
      wt_block G Γ (Breset blocks er)

  | wt_Bswitch : forall Γ ec branches tx tn,
      wt_exp G Γ ec ->
      typeof ec = [Tenum tx tn] ->
      In (Tenum tx tn) G.(types) ->
      Permutation (map fst branches) (seq 0 (length tn)) ->
      branches <> nil ->
      Forall (fun blks => wt_branch (Forall (wt_block G Γ)) (snd blks)) branches ->
      wt_block G Γ (Bswitch ec branches)

  | wt_BautoWeak : forall Γ ini oth states ck,
      wt_clock G.(types) Γ ck ->
      Forall (fun '(e, t) => wt_exp G Γ e /\ typeof e = [bool_velus_type] /\ InMembers t (map fst states)) ini ->
      InMembers oth (map fst states) ->
      Permutation (map fst (map fst states)) (seq 0 (length states)) ->
      NoDup (map snd (map fst states)) ->
      states <> [] ->
      Forall (fun blks =>
                wt_branch
                  (fun blks =>
                     fst blks = []
                     /\ wt_scope (fun Γ' blks => Forall (wt_block G Γ') (fst blks)
                                             /\ Forall (fun '(e, (t, _)) => wt_exp G Γ' e
                                                                        /\ typeof e = [bool_velus_type]
                                                                        /\ InMembers t (map fst states)) (snd blks))
                         G Γ (snd blks))
                  (snd blks)) states ->
      wt_block G Γ (Bauto Weak ck (ini, oth) states)

  | wt_BautoStrong : forall Γ oth states ck,
      wt_clock G.(types) Γ ck ->
      InMembers oth (map fst states) ->
      Permutation (map fst (map fst states)) (seq 0 (length states)) ->
      NoDup (map snd (map fst states)) ->
      states <> [] ->
      Forall (fun blks =>
                wt_branch
                  (fun blks =>
                     Forall (fun '(e, (t, _)) => wt_exp G Γ e
                                              /\ typeof e = [bool_velus_type]
                                              /\ InMembers t (map fst states)) (fst blks)
                     /\ wt_scope (fun Γ' blks => Forall (wt_block G Γ') (fst blks) /\ snd blks = [])
                         G Γ (snd blks))
                  (snd blks)) states ->
      wt_block G Γ (Bauto Strong ck ([], oth) states)

  | wt_Blocal: forall Γ scope,
      wt_scope (fun Γ' => Forall (wt_block G Γ')) G Γ scope ->
      wt_block G Γ (Blocal scope).

  Inductive wt_node {PSyn prefs} (G: @global PSyn prefs) : @node PSyn prefs -> Prop :=
  | wt_Node : forall n,
      let Γ := senv_of_ins n.(n_in) ++ senv_of_decls n.(n_out) in
      wt_clocks G.(types) (senv_of_ins n.(n_in)) (senv_of_ins n.(n_in)) ->
      wt_clocks G.(types) Γ (senv_of_decls n.(n_out)) ->
      Forall (fun '(_, ann) => wt_type G.(types) ann.(typ)) Γ ->
      wt_block G Γ n.(n_block) ->
      wt_node G n.

  Definition wt_global {PSyn prefs} (G: @global PSyn prefs) : Prop :=
    wt_type G.(types) bool_velus_type /\
    wt_program wt_node G.

  Global Hint Constructors wt_type wt_clock wt_exp wt_block wt_node : ltyping.
  Global Hint Unfold wt_equation : ltyping.

  Ltac inv_exp :=
    match goal with
    | H:wt_exp _ _ _ |- _ => inv H
    end.

  Ltac inv_scope :=
    match goal with
    | H:wt_scope _ _ _ _ |- _ => inv H
    end;
    destruct_conjs; subst.

  Ltac inv_branch :=
    match goal with
    | H:wt_branch _ _ |- _ => inv H
    end;
    destruct_conjs; subst.

  Ltac inv_block :=
    match goal with
    | H:wt_block _ _ _ |- _ => inv H
    end.

  Lemma wt_global_NoDup {PSyn prefs}:
    forall (g : @global PSyn prefs),
      wt_global g ->
      NoDup (map name (nodes g)).
  Proof.
    intros * (?&Wt).
    eapply wt_program_NoDup in Wt; eauto.
  Qed.

  Lemma wt_global_cons {PSyn prefs} :
    forall tys (nd : @node PSyn prefs) nds exts,
      wt_global (Global tys exts (nd :: nds)) ->
      wt_global (Global tys exts nds).
  Proof.
    inversion 1 as [? Hi]. inv Hi.
    constructor; auto.
  Qed.

  Lemma wt_global_uncons {PSyn prefs} :
    forall tys (nd : @node PSyn prefs) nds exts,
      wt_global (Global tys exts (nd :: nds)) ->
      wt_node (Global tys exts nds) nd.
  Proof.
    intros * [? Wt]. now inv Wt.
  Qed.

  Lemma wt_find_node {PSyn prefs}:
    forall (G : @global PSyn prefs) f n,
      wt_global G ->
      find_node f G = Some n ->
      exists G', wt_node G' n /\ types G' = types G.
  Proof.
    intros G f n' (?&Hwt) Hfind.
    apply option_map_inv in Hfind as ((?&?)&(?&?)); subst.
    eapply wt_program_find_unit' in Hwt as (?&?&Hequiv); [|eauto].
    eexists; split; eauto.
    apply equiv_program_types in Hequiv; auto.
  Qed.

  Lemma wt_clock_add:
    forall x v types env ck,
      ~InMembers x env ->
      wt_clock types env ck ->
      wt_clock types ((x, v) :: env) ck.
  Proof.
    induction ck; auto with ltyping.
    inversion 2; subst.
    eauto with ltyping datatypes senv.
  Qed.

  Global Instance wt_clock_Proper types:
    Proper (@Permutation.Permutation _ ==> @eq clock ==> iff)
           (wt_clock types).
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

  Global Instance wt_clock_types_Proper :
    Proper (@incl _ ==> @eq _ ==> @eq _ ==> Basics.impl) wt_clock.
  Proof.
    intros ?? Same ??? ? ck ? Wt; subst.
    induction ck; inversion_clear Wt; subst; repeat constructor; auto.
  Qed.

  Global Instance wt_clock_pointwise_Proper types :
    Proper (@Permutation.Permutation _
                                     ==> pointwise_relation clock iff)
           (wt_clock types).
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
    split; intro H; induction e using exp_ind2; inv H; econstructor; simpl_Forall; eauto;
      match goal with
      | |- HasType env' _ _ => now rewrite Henv
      | |- HasType env _ _ => now rewrite <-Henv
      | |- IsLast env' _ => now rewrite Henv
      | |- IsLast env _ => now rewrite <-Henv
      | |- wt_clock _ env' _ => now rewrite Henv
      | |- wt_clock _ env _ => now rewrite <-Henv
      end.
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

    Fact wt_clock_incl : forall types Γ Γ' cl,
        (forall x ty, HasType Γ x ty -> HasType Γ' x ty) ->
        wt_clock types Γ cl ->
        wt_clock types Γ' cl.
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
      intros * Hincl1 Hincl2 Hwt;
        induction e using exp_ind2; inv Hwt;
        econstructor; simpl_Forall; eauto with senv ltyping.
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
      assert (forall x ty, HasType (Γ ++ senv_of_decls locs) x ty -> HasType (Γ' ++ senv_of_decls locs) x ty) as Hty'.
      { intros *. rewrite 2 HasType_app. intros [|]; auto. }
      assert (forall x, IsLast (Γ ++ senv_of_decls locs) x -> IsLast (Γ' ++ senv_of_decls locs) x) as Hl'.
      { intros *. rewrite 2 IsLast_app. intros [|]; auto. }
      inv Hwt. econstructor; eauto.
      - unfold wt_clocks in *; simpl_Forall; eauto using wt_clock_incl.
    Qed.

    Lemma wt_block_incl {PSyn prefs} : forall (G: @global PSyn prefs) d Γ Γ',
        (forall x ty, HasType Γ x ty -> HasType Γ' x ty) ->
        (forall x, IsLast Γ x -> IsLast Γ' x) ->
        wt_block G Γ d ->
        wt_block G Γ' d .
    Proof.
      induction d using block_ind2; intros * Incl1 Incl2 Wt; inv_block.
      - constructor. eauto using wt_equation_incl.
      - econstructor; eauto using wt_exp_incl.
      - econstructor; eauto using wt_exp_incl.
        simpl_Forall; eauto.
      - econstructor; eauto using wt_exp_incl.
        simpl_Forall; eauto.
        destruct b. take (wt_branch _ _) and inv it. constructor.
        simpl_Forall; eauto.
      - econstructor; auto; simpl_Forall; eauto using wt_exp_incl, wt_clock_incl.
        inv_branch. constructor.
        split; auto.
        destruct s. eapply wt_scope_incl; eauto.
        intros * Hty' Hl' (?&?); split; simpl_Forall; eauto using wt_exp_incl.
      - econstructor; auto; simpl_Forall; eauto using wt_exp_incl, wt_clock_incl.
        inv_branch. constructor.
        split; simpl_Forall; eauto using wt_exp_incl.
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
      Forall (wt_clock G.(types) Γ) (clockof e).
  Proof.
    intros * Hwt. simpl_Forall.
    inv Hwt; simpl in *;
      repeat match goal with
             | H: _ \/ _ |- _ => destruct H; subst
             | H: False |- _ => inv H
             end; auto with ltyping;
      simpl_In; simpl_Forall; eauto.
  Qed.

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

  (** ** Validation *)
  Section ValidateExpression.

    Context {PSyn : list decl -> block -> Prop}.
    Context {prefs : PS.t}.

    Variable G : @global PSyn prefs.
    Variable tenv : Env.t type.
    Variable extenv : Env.t (list ctype * ctype).
    Variable venv venvl : Env.t type.
    Variable env : static_env.

    Hypothesis Htypes : forall x ty, Env.find x tenv = Some ty -> wt_type G.(types) ty.
    Hypothesis Hexterns : forall x ty, Env.find x extenv = Some ty -> In (x, ty) G.(externs).
    Hypothesis Henv : forall x ty, Env.find x venv = Some ty -> HasType env x ty.
    Hypothesis Henvl : forall x ty, Env.find x venvl = Some ty -> HasType env x ty /\ IsLast env x.

    Open Scope option_monad_scope.

    Definition check_type_in ty : bool :=
      match ty with
      | Tenum x n =>
          match Env.find x tenv with
          | Some ty' => ty' ==b ty
          | None => false
          end
      | _ => true
      end.

    Lemma check_type_in_correct : forall ty,
        check_type_in ty = true ->
        wt_type G.(types) ty.
    Proof.
      unfold check_type_in.
      intros * Hc. cases_eqn Eq; auto using wt_type.
      rewrite equiv_decb_equiv in Hc; inv Hc.
      eauto.
    Qed.

    Opaque check_type_in.

    Fixpoint check_clock (ck : clock) : bool :=
      match ck with
      | Cbase => true
      | Con ck' x (ty, k) =>
          match Env.find x venv with
          | Some (Tenum xt n) => (ty ==b Tenum xt n)
                                && (k <? length n)
                                && check_type_in ty
                                && check_clock ck'
          | _ => false
          end
      end.

    Lemma check_clock_correct:
      forall ck,
        check_clock ck = true ->
        wt_clock G.(types) env ck.
    Proof.
      induction ck; intros CC. now constructor.
      simpl in CC. cases_eqn Heq; subst.
      repeat rewrite Bool.andb_true_iff in CC; destruct CC as (((CC1 & CC2) & CC3) & CC4).
      rewrite equiv_decb_equiv in CC1; inv CC1.
      apply Nat.ltb_lt in CC2.
      apply check_type_in_correct in CC3; inv CC3.
      econstructor; eauto.
    Qed.

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

    Definition check_paired_types2 (t1 : type) (tc : ann) : bool :=
      let '(t, c) := tc in
      (t1 ==b t) && (check_clock c).

    Definition check_paired_types3 (t1 t2 : type) (tc : ann) : bool :=
      let '(t, c) := tc in
      (t1 ==b t) && (t2 ==b t) && (check_clock c).

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

    Fixpoint check_exp (e : exp) : option (list type) :=
      match e with
      | Econst c => Some ([Tprimitive (ctype_cconst c)])

      | Eenum k (Tenum xt n) =>
        if check_type_in (Tenum xt n) && (k <? length n) then Some [Tenum xt n] else None

      | Evar x (xt, nck) =>
        if check_var x xt && check_clock nck then Some [xt] else None

      | Elast x (xt, nck) =>
        if check_last x xt && check_clock nck then Some [xt] else None

      | Eunop op e (xt, nck) =>
        do te <- assert_singleton (check_exp e);
        do t <- type_unop op te;
        if (xt ==b t) && check_type_in t && check_clock nck then Some [xt] else None

      | Ebinop op e1 e2 (xt, nck) =>
        do te1 <- assert_singleton (check_exp e1);
        do te2 <- assert_singleton (check_exp e2);
        do t <- type_binop op te1 te2;
        if (xt ==b t) && check_type_in t && check_clock nck then Some [xt] else None

      | Eextcall f es (tyout, ck) =>
          do tyins <- oconcat (map check_exp es);
          match Env.find f extenv with
          | Some (ctyins, ctyout) =>
              if (ctyout ==b tyout)
                 && (List.map Tprimitive ctyins ==b tyins)
                 && check_clock ck
                 && negb (is_nil (typesof es))
              then Some [Tprimitive ctyout] else None
          | None => None
          end

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

      | Ewhen es (x, Tenum xt n) k (tys, nck) =>
        do ts <- oconcat (map check_exp es);
        if check_var x (Tenum xt n)
           && check_type_in (Tenum xt n)
           && (k <? length n)
           && (forall2b equiv_decb ts tys)
           && (check_clock nck)
        then Some tys else None

      | Emerge (x, Tenum xt n) es (tys, nck) =>
        do tss <- omap (fun es => oconcat (map check_exp (snd es))) es;
        if check_var x (Tenum xt n) && check_type_in (Tenum xt n)
           && (check_perm_seq (map fst es) (length n)) && (negb (is_nil es))
           && (forallb (fun ts => forall2b equiv_decb ts tys) tss)
           && (check_clock nck)
        then Some tys else None

      | Ecase e brs None (tys, nck) =>
        do tss <- omap (fun es => oconcat (map check_exp (snd es))) brs;
        (* do tds <- oconcat (map check_exp d); *)
        do xt <- assert_singleton (check_exp e);
        match xt with
        | Tenum xt n =>
          if check_type_in (Tenum xt n)
             && (check_perm_seq (map fst brs) (length n)) && (negb (is_nil brs))
             && (forallb (fun ts => (forall2b equiv_decb ts tys)) tss)
             && (check_clock nck)
          then Some tys else None
        | _ => None
        end

      | Ecase e brs (Some d) (tys, nck) =>
        do tss <- omap (fun es => oconcat (map check_exp (snd es))) brs;
        do tds <- oconcat (map check_exp d);
        do xt <- assert_singleton (check_exp e);
        match xt with
        | Tenum xt n =>
          if check_type_in (Tenum xt n)
             && (check_nodup_nat (map fst brs)) && (forallb (fun i => i <? length n) (map fst brs)) && (negb (is_nil brs))
             && (forallb (fun ts => (forall2b equiv_decb ts tys)) (tds::tss))
             && (check_clock nck)
          then Some tys else None
        | _ => None
        end

      | Eapp f es er anns =>
        do n <- find_node f G;
        do ts <- oconcat (map check_exp es);
        do tr <- omap check_exp er;
        if (forall2b (fun et '(_, (t, _, _)) => et ==b t) ts n.(n_in))
             && (forall2b (fun '(ot, oc) '(_, (t, _, _, _)) =>
                             check_clock oc
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

    Lemma check_type_in_correct':
      forall tx n,
        check_type_in (Tenum tx n) = true ->
        In (Tenum tx n) G.(types) /\ 0 < length n.
    Proof.
      intros * CC.
      apply check_type_in_correct in CC. now inv CC.
    Qed.
    (* Local Hint Resolve check_enum_correct' : ltyping. *)

    Lemma check_paired_types2_correct:
      forall tys1 anns,
        forall2b check_paired_types2 tys1 anns = true ->
        tys1 = map fst anns
        /\ Forall (wt_clock G.(types) env) (map snd anns).
    Proof.
      setoid_rewrite forall2b_Forall2.
      induction 1 as [|ty1 (ty, nck) tys1 anns IH1 IH3];
        subst; simpl; eauto.
      simpl in IH1.
      repeat rewrite Bool.andb_true_iff in IH1.
      setoid_rewrite equiv_decb_equiv in IH1.
      destruct IH1 as (-> & IH1).
      eapply check_clock_correct in IH1; eauto.
      destruct IHIH3; split; try f_equal; auto.
    Qed.

    Lemma check_paired_types3_correct:
      forall tys1 tys2 anns,
        forall3b check_paired_types3 tys1 tys2 anns = true ->
        tys1 = map fst anns
        /\ tys2 = map fst anns
        /\ Forall (wt_clock G.(types) env) (map snd anns).
    Proof.
      setoid_rewrite forall3b_Forall3.
      induction 1 as [|ty1 ty2 (ty, nck) tys1 tys2 anns IH1 IH2 (? & ? & IH3)];
        subst; simpl; eauto.
      simpl in IH1.
      repeat rewrite Bool.andb_true_iff in IH1.
      setoid_rewrite equiv_decb_equiv in IH1.
      destruct IH1 as ((-> & ->) & IH1).
      eapply check_clock_correct in IH1; eauto.
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
    Proof.
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
    Proof.
      induction es as [|e es IH]; intros tys WTf CE. now inv CE; auto.
      simpl in CE. destruct (f e) eqn:Ce; [|now omonadInv CE].
      destruct (omap f es) as [tes|]; [|now omonadInv CE].
      omonadInv CE. simpl.
      apply WTf in Ce as (Ce1 & ?); auto with datatypes.
      destruct (IH tes) as (? & ?); auto with datatypes.
    Qed.

    Import Permutation.
    Local Hint Constructors wt_exp wt_block : ltyping.
    Lemma check_exp_correct:
      forall e tys,
        check_exp e = Some tys ->
        wt_exp G env e
        /\ typeof e = tys.
    Proof with eauto with ltyping.
      induction e using exp_ind2; simpl; intros tys CE. 12:destruct d; simpl in *.
      all:repeat progress
            match goal with
            | a:ann |- _ => destruct a
            | a:lann |- _ => destruct a
            | _: _ * _ |- _ => destruct_conjs
            | H:obind _ _ = Some _ |- _ => omonadInv H
            | H:obind2 _ _ = Some _ |- _ => omonadInv H
            | H:obind ?v _ = Some _ |- _ =>
                let OE:=fresh "OE0" in destruct v eqn:OE; [simpl in H|now omonadInv H]
            | H: _ && _ = true |- _ => apply Bool.andb_true_iff in H as (? & ?)
            | H: ((_ ==b _) = true) |- _ => rewrite equiv_decb_equiv in H; inv H
            | H: check_clock _ = true |- _ => eapply check_clock_correct in H; eauto
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
                | Tprimitive _ => None | Tenum _ _ => _
                end = Some _ |- _ => destruct ty as [|]; try congruence
            | H:None = Some _ |- _ => discriminate
            | H:Some _ = Some _ |- _ => inv H
            | H:assert_singleton _ = Some _ |- _ => apply assert_singleton_spec in H
            | H:check_var _ _ = true |- _ => eapply check_var_correct in H; eauto
            | H:check_type_in _ = true |- _ => apply check_type_in_correct in H
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

      - (* Elast *)
        eapply check_last_correct in H as (?&?)...
      - (* Eunop *)
        apply IHe in OE0 as (? & ?)...
      - (* Ebinop *)
        apply IHe1 in OE0 as (? & ?); apply IHe2 in OE1 as (? & ?)...
      - (* Eextcall *)
        take (Forall _ es) and rewrite Forall_forall in it.
        apply oconcat_map_check_exp' in OE0 as (? & ?)...
        split; auto.
        econstructor; eauto.
        + take (typesof _ = _) and rewrite it. simpl_Forall; auto.
        + apply Bool.negb_true_iff, Bool.not_true_iff_false in H1.
          contradict H1. now apply is_nil_spec.
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
        take (wt_type _ _) and inv it...
      - (* Emerge *)
        take (Forall _ es) and (repeat setoid_rewrite Forall_forall in it).
        take (omap _ _ = Some _) and
             apply omap_concat_map_check_exp' in it as (Hwt & Hty); eauto.
        econstructor; eauto. econstructor; eauto.
        + take (wt_type _ _) and inv it...
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
        + take (wt_type _ _) and inv it...
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
        + take (wt_type _ _) and inv it...
        + eapply check_perm_seq_spec in H5...
        + contradict H4; subst; simpl. auto.
        + eapply Forall2_ignore2 in Hty. simpl_Forall.
          take (Forall2 eq _ _) and apply Forall2_eq in it. congruence.
      - (* Eapp *)
        take (Forall _ es) and rewrite Forall_forall in it.
        take (Forall _ er) and rewrite Forall_forall in it.
        take (oconcat (map check_exp _) = Some _) and
             apply oconcat_map_check_exp' in it as (? & ?); auto.
        take (omap check_exp _ = Some _) and
             apply omap_check_exp' in it as (? & ?); auto.
        split; auto. subst.
        assert (Forall2 (fun et '(_, (t, _, _)) => et = t) (typesof es) n.(n_in)).
        { simpl_Forall. now apply equiv_decb_equiv. }
        assert (Forall2 (fun ann '(_, (t, _, _, _)) => fst ann = t) a n.(n_out)).
        { simpl_Forall.
          take (_ && _ = true) and apply Bool.andb_true_iff in it as (EQ1 & EQ2).
          now rewrite equiv_decb_equiv in EQ2. }
        assert (Forall (fun ann => wt_clock G.(types) env (snd ann)) a).
        { repeat take (Forall2 _ _ n.(n_out)) and apply Forall2_ignore2 in it.
          simpl_Forall.
          take (_ = true) and apply Bool.andb_true_iff in it as (EQ1 & EQ2).
          eapply check_clock_correct in EQ1; eauto.
        }
        econstructor; eauto; simpl in *;
          clear it; cases_eqn E; subst.
        eapply check_reset_correct in H2.
        eapply Forall2_ignore1' in H2. 2:symmetry; eapply Forall2_length; eauto.
        eapply Forall2_Forall2, Forall2_ignore2 in H5; eauto.
        simpl_Forall. congruence.
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
    Context {PSyn : list decl -> block -> Prop}.
    Context {prefs : PS.t}.
    Variable (G : @global PSyn prefs).

    Variable (tenv : Env.t type).
    Variable extenv : Env.t (list ctype * ctype).
    Hypothesis Htypes : forall x ty, Env.find x tenv = Some ty -> wt_type G.(types) ty.
    Hypothesis Hexterns : forall x ty, Env.find x extenv = Some ty -> In (x, ty) G.(externs).

    Definition check_tag {A} (l : list ((enumtag * ident) * A)) (x : enumtag) :=
      existsb (fun '((y, _), _) => x =? y) l.

    Lemma check_tag_correct {A} : forall (l : list (_ * A)) x,
        check_tag l x = true ->
        InMembers x (map fst l).
    Proof.
      intros * Hc. unfold check_tag in Hc.
      rewrite <-Exists_existsb with (P:=fun y => x = fst (fst y)) in Hc.
      2:intros; destruct_conjs; simpl; rewrite Nat.eqb_eq; reflexivity.
      simpl_Exists; subst; eapply In_InMembers. solve_In.
    Qed.

    Definition check_bool_exp venv venvl e :=
      match check_exp G tenv extenv venv venvl e with
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
      let venv' := Env.adds' (map (fun '(x, (ty, _, _, _)) => (x, ty)) locs) venv in
      let venvl' := Env.adds' (map_filter (fun '(x, (ty, _, _, o)) => option_map (fun _ => (x, ty)) o) locs) venvl in
      forallb (check_clock tenv venv') (map (fun '(_, (_, ck, _, _)) => ck) locs)
      && forallb (check_type_in tenv) (map (fun '(x, (ty, _, _, _)) => ty) locs)
      && f_check venv' venvl' blks.

    Fixpoint check_block (venv venvl : Env.t type) (d : block) : bool :=
      match d with
      | Beq eq => check_equation G tenv extenv venv venvl eq
      | Blast x e =>
          match assert_singleton (check_exp G tenv extenv venv venvl e) with
          | Some ty => check_last venvl x ty
          | _ => false
          end
      | Breset blocks er =>
          forallb (check_block venv venvl) blocks
          && check_bool_exp venv venvl er
      | Bswitch ec brs =>
        match assert_singleton (check_exp G tenv extenv venv venvl ec) with
        | Some (Tenum xt n) =>
            check_type_in tenv (Tenum xt n)
            && check_perm_seq (map fst brs) (length n)
            && (negb (is_nil brs))
            && forallb (fun '(_, Branch _ blks) => forallb (check_block venv venvl) blks) brs
        | _ => false
        end
      | Bauto Weak ck (ini, oth) states =>
          check_clock tenv venv ck
          && forallb (fun '(e, t) => check_bool_exp venv venvl e && check_tag states t) ini
          && check_tag states oth
          && check_perm_seq (map fst (map fst states)) (length states)
          && check_nodup (map snd (map fst states))
          && (negb (is_nil states))
          && forallb (fun '(_, Branch _ (unl, blks)) =>
                        is_nil unl
                        && check_scope (fun venv' venvl' '(blks, trans) =>
                                          forallb (check_block venv' venvl') blks
                                          && forallb (fun '(e, (t, _)) => check_bool_exp venv' venvl' e
                                                                       && check_tag states t) trans) venv venvl blks)
                     states
      | Bauto Strong ck (ini, oth) states =>
          check_clock tenv venv ck
          && is_nil ini
          && check_tag states oth
          && check_perm_seq (map fst (map fst states)) (length states)
          && check_nodup (map snd (map fst states))
          && (negb (is_nil states))
          && forallb (fun '(_, Branch _ (unl, blks)) =>
                        forallb (fun '(e, (t, _)) => check_bool_exp venv venvl e && check_tag states t) unl
                        && check_scope (fun venv' venvl' '(blks, trans) =>
                                          forallb (check_block venv' venvl') blks
                                          && is_nil trans) venv venvl blks)
                     states
      | Blocal s =>
          check_scope (fun venv' venvl' => forallb (check_block venv' venvl')) venv venvl s
      end.

    Definition check_node (n : @node PSyn prefs) :=
      let ins := List.map (fun '(x, (ty, _, _)) => (x, ty)) (n_in n) in
      let outs := List.map (fun '(x, (ty, _, _, _)) => (x, ty)) (n_out n) in
      let insouts := ins++outs in
      let venv := Env.from_list (ins++outs) in
      let venvl := Env.from_list (map_filter (fun '(x, (ty, _, _, o)) => option_map (fun _ => (x, ty)) o) (n_out n)) in
      forallb (check_clock tenv (Env.from_list ins)) (List.map (fun '(_, (_, ck, _)) => ck) (n_in n))
      && forallb (check_clock tenv venv) (List.map (fun '(_, (_, ck, _, _)) => ck) (n_out n))
      && forallb (check_type_in tenv) (map snd insouts)
      && check_block venv venvl (n_block n).

    Hint Constructors wt_block : ltyping.
    Import Permutation.

    Opaque check_type_in.

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
      assert (forall x ty, Env.find x (Env.adds' (map (fun '(x, (ty, _, _, _)) => (x, ty)) locs) venv) = Some ty ->
                        HasType (env ++ senv_of_decls locs) x ty) as Henv'.
        { intros * Hfind. apply Env.find_adds'_In in Hfind as [Hfind|Hfind].
          - simpl_In. right. econstructor. solve_In. reflexivity.
          - apply Henv in Hfind. inv Hfind. eauto with senv datatypes.
        }
        assert (forall x ty,
                   Env.find x (Env.adds' (map_filter (fun '(x, (ty, _, _, o)) => option_map (fun _ => (x, ty)) o) locs) venvl) = Some ty ->
                   HasType (env ++ senv_of_decls locs) x ty /\ IsLast (env ++ senv_of_decls locs) x) as Henvl'.
        { intros * Hfind. apply Env.find_adds'_In in Hfind as [Hfind|Hfind].
          - simpl_In.
            split; right; econstructor. 1,3:solve_In. reflexivity. simpl. congruence.
          - apply Henvl in Hfind as (Hhas&His). inv Hhas. inv His.
            constructor; eauto with senv datatypes.
        }
        simpl in *.
      repeat rewrite Bool.andb_true_iff in Hc. destruct Hc as ((CC&CE)&CB).
      apply forallb_Forall in CC. apply forallb_Forall in CE.
      econstructor; eauto.
      - unfold wt_clocks, senv_of_decls. simpl_Forall.
        eapply check_clock_correct in CC; eauto.
      - simpl_Forall. eapply check_type_in_correct; eauto.
    Qed.

    Lemma check_block_correct : forall blk venv venvl env,
        (forall x ty, Env.find x venv = Some ty -> HasType env x ty) ->
        (forall x ty, Env.find x venvl = Some ty -> HasType env x ty /\ IsLast env x) ->
        check_block venv venvl blk = true ->
        wt_block G env blk.
    Proof.
      Opaque check_scope.
      induction blk using block_ind2; intros * Henv Henvl CD; simpl in *. 5:destruct type0.
      - (* equation *)
        eapply check_equation_correct in CD; eauto with ltyping.
      - (* last *)
        cases_eqn EQ.
        eapply assert_singleton_spec, check_exp_correct in EQ as (Hwt1&Hwt2); eauto.
        eapply check_last_correct in CD as (Ty&L); eauto.
        econstructor; eauto.
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
        eapply check_type_in_correct' in CE as (?&?); simpl in *; eauto.
        econstructor; eauto.
        + eapply check_perm_seq_spec; eauto.
        + contradict CL; subst; simpl in *. auto.
        + eapply forallb_Forall in CBrs. simpl_Forall.
          destruct b. constructor.
          eapply forallb_Forall in CBrs. simpl_Forall; eauto.
      - (* automaton (weak) *)
        destruct_conjs. repeat rewrite Bool.andb_true_iff in CD.
        destruct CD as ((((((CC&CI)&CO)&CP)&CND)&CN)&CB).
        repeat (take (forallb _ _ = true) and apply forallb_Forall in it).
        constructor; eauto using check_tag_correct; simpl_Forall.
        + eapply check_clock_correct in CC; eauto.
        + apply Bool.andb_true_iff in it as (Hce&Htag).
          eapply check_bool_exp_correct in Hce as (?&?); eauto using check_tag_correct.
        + apply check_perm_seq_spec; auto.
        + now apply check_nodup_correct.
        + contradict CN; subst; simpl in *. auto.
        + destruct b as [?(?&[?(?&?)])]. rewrite Bool.andb_true_iff, is_nil_spec in it0. destruct it0. constructor. split; auto.
          eapply check_scope_correct; eauto.
          intros * ?? Hc; simpl in *.
          rewrite Bool.andb_true_iff, 2 forallb_Forall in Hc. destruct Hc as (?&CT).
          split; simpl_Forall; eauto.
          apply Bool.andb_true_iff in CT as (CE&?).
          eapply check_bool_exp_correct in CE as (?&?); eauto using check_tag_correct.
      - (* automaton (strong) *)
        destruct_conjs. repeat rewrite Bool.andb_true_iff in CD.
        destruct CD as ((((((CC&CI)&CO)&CP)&CND)&CN)&CB).
        repeat (take (forallb _ _ = true) and apply forallb_Forall in it).
        apply is_nil_spec in CI; subst.
        constructor; eauto using check_tag_correct; simpl_Forall.
        + eapply check_clock_correct in CC; eauto.
        + apply check_perm_seq_spec; auto.
        + now apply check_nodup_correct.
        + contradict CN; subst; simpl in *. auto.
        + destruct b as [?(?&[?(?&?)])].
          rewrite Bool.andb_true_iff, forallb_Forall in it. destruct it. constructor; split.
          * simpl_Forall.
            apply Bool.andb_true_iff in H1 as (CE&?).
            eapply check_bool_exp_correct in CE as (?&?); eauto using check_tag_correct.
          * eapply check_scope_correct; eauto.
            intros * ?? Hc; simpl in *.
            rewrite Bool.andb_true_iff, is_nil_spec, forallb_Forall in Hc. destruct Hc as (?&CT).
            split; simpl_Forall; eauto.

      - (* local *)
        constructor. eapply check_scope_correct; eauto.
        intros * ?? Hc. apply forallb_Forall in Hc.
        simpl_Forall; eauto.
        Transparent check_scope.
    Qed.

    Lemma check_node_correct : forall n,
        check_node n = true ->
        wt_node G n.
    Proof.
      intros * Hcheck.
      specialize (n_nodup n) as (Hdndup1&_).
      unfold check_node in Hcheck.
      repeat rewrite Bool.andb_true_iff in Hcheck. destruct Hcheck as [[[Hc1 Hc2] Hc3] Hc4].
      apply forallb_Forall in Hc1, Hc2, Hc3.
      assert (forall x ty, Env.find x (Env.from_list (map (fun '(x, (ty, _, _)) => (x, ty)) (n_in n) ++ map (fun '(x, (ty, _, _, _)) => (x, ty)) (n_out n))) = Some ty ->
                      HasType (senv_of_ins (n_in n) ++ senv_of_decls (n_out n)) x ty) as Henv.
      { intros * Hfind. clear - Hfind. apply Env.from_list_find_In in Hfind. rewrite HasType_app.
        apply in_app_iff in Hfind as [Hfind|Hfind]; [left|right]; simpl_In; econstructor; solve_In; reflexivity. }
      assert (forall (x : Env.key) (ty : type),
                 Env.find x (Env.from_list (map_filter (fun '(x0, (ty0, _, _, o)) => option_map (fun _ : ident => (x0, ty0)) o) (n_out n))) = Some ty ->
                 HasType (senv_of_ins (n_in n) ++ senv_of_decls (n_out n)) x ty /\ IsLast (senv_of_ins (n_in n) ++ senv_of_decls (n_out n)) x) as Henvl.
      { intros * Hfind. clear - Hfind. apply Env.from_list_find_In in Hfind. simpl_In.
        split; right; econstructor; solve_In; simpl; congruence. }
      econstructor; autounfold with list in *.
      1-2:(unfold wt_clocks; simpl_Forall;
           take (check_clock _ _ _ = _) and eapply check_clock_correct in it; eauto;
           try rewrite Hincl in it; eauto).
      - intros * Hfind. apply Env.from_list_find_In in Hfind. simpl_In.
        econstructor. solve_In. reflexivity.
      - rewrite map_app, Forall_app in Hc3. destruct Hc3.
        apply Forall_app; split; simpl_Forall; eauto using check_type_in_correct.
      - eapply check_block_correct in Hc4; eauto.
    Qed.

  End ValidateBlock.

  Section ValidateGlobal.
    Definition check_type (tenv : Env.t type) (ty : type) :=
      check_type_in tenv ty
      && match ty with
         | Tprimitive _ => true
         | Tenum tx tn => (0 <? length tn) && check_nodup tn
         end.

    Lemma check_type_correct {PSyn prefs} (G : @global PSyn prefs) :
      forall tenv ty,
        (forall x ty, Env.find x tenv = Some ty -> In ty (types G)) ->
        check_type tenv ty = true ->
        wt_type (types G) ty.
    Proof.
      intros * Htypes CC.
      unfold check_type, check_type_in in *.
      apply Bool.andb_true_iff in CC as (CC1 & CC2).
      cases_eqn Eq; auto using wt_type.
      apply Bool.andb_true_iff in CC2 as (CC2 & CC3).
      rewrite equiv_decb_equiv in CC1; inv CC1.
      constructor; eauto using check_nodup_correct.
       now apply Nat.ltb_lt.
    Qed.

    Opaque check_type_in check_type.

    Definition check_global {PSyn prefs} (G : @global PSyn prefs) :=
      let eenv := Env.from_list
                    (map_filter (fun ty => match ty with
                                        | Tenum tx tn => Some (tx, ty)
                                        | _ => None
                                        end) G.(types)) in
      let extenv := Env.from_list G.(externs) in

      forallb (check_type eenv) G.(types)
      && check_type_in eenv bool_velus_type
      && check_nodup (List.map n_name G.(nodes))
      && (fix aux nds := match nds with
                         | [] => true
                         | hd::tl => check_node (update G tl) eenv extenv hd && aux tl
                         end) G.(nodes).

    Lemma check_global_correct {PSyn prefs} : forall (G: @global PSyn prefs),
        check_global G = true ->
        wt_global G.
    Proof.
      intros G Hcheck.
      unfold check_global in Hcheck.
      repeat rewrite Bool.andb_true_iff in Hcheck. destruct Hcheck as [[[Htys Hbool] Hndup] Hcheck].
      assert (Forall (wt_type G.(types)) G.(types)) as Htypes; [|clear Htys].
      { apply forallb_Forall in Htys. simpl_Forall.
        eapply check_type_correct; [|eauto].
        intros * Hfind. apply Env.from_list_find_In in Hfind; simpl_In.
        destruct x1; now inv Hf. }
      remember (Env.from_list _) as tenv.
      assert (forall x ty, Env.find x tenv = Some ty -> wt_type (types G) ty) as Htys; [|clear Heqtenv].
      { intros * Hfind. subst. apply Env.from_list_find_In in Hfind; simpl_In.
        simpl_Forall.
        destruct x0; inv Hf; auto. }
      split.
      - eapply check_type_in_correct in Hbool; eauto.
      - apply check_nodup_correct in Hndup.
        unfold wt_program, units; simpl.
        induction (nodes G); constructor; inv Hndup.
        1-2:simpl in Hcheck; apply Bool.andb_true_iff in Hcheck as [Hc1 Hc2]; auto.
        split.
        + apply check_node_correct in Hc1; auto using Env.from_list_find_In.
        + apply Forall_forall. intros ? Hin contra.
          apply H1. rewrite in_map_iff. exists x; split; auto.
    Qed.
  End ValidateGlobal.

  Section interface_incl.
    Context {PSyn1 PSyn2 : list decl -> block -> Prop}.
    Context {prefs1 prefs2 : PS.t}.
    Variable G1 : @global PSyn1 prefs1.
    Variable G2 : @global PSyn2 prefs2.

    Hypothesis Heq : global_iface_incl G1 G2.

    Fact iface_incl_wt_clock : forall vars ck,
        wt_clock G1.(types) vars ck ->
        wt_clock G2.(types) vars ck.
    Proof.
      induction ck; intros * Hwt; inv Hwt; constructor; auto.
      apply Heq; auto.
    Qed.

    Lemma iface_incl_wt_type : forall ty,
        wt_type G1.(types) ty ->
        wt_type G2.(types) ty.
    Proof.
      induction ty; intros * Henum; inv Henum; auto with ltyping.
      constructor; eauto; eapply Heq; eauto.
    Qed.
    Hint Resolve iface_incl_wt_type iface_incl_wt_clock : ltyping.

    Hint Constructors wt_exp : ltyping.
    Fact iface_incl_wt_exp : forall Γ e,
        wt_exp G1 Γ e ->
        wt_exp G2 Γ e.
    Proof with eauto with ltyping.
      induction e using exp_ind2; intros Hwt; inv Hwt...
      1-8:econstructor; simpl_Forall; eauto with ltyping.
      all:try apply Heq; auto.
      - eapply Heq in H7 as (?&Hfind'&(?&?&?&?)).
        econstructor; simpl_Forall; eauto with ltyping.
        + eapply Forall2_eq in H3. simpl_Forall. eapply Forall2_trans_ex in H3; [|eauto].
          simpl_Forall. inv_equalities. auto.
        + eapply Forall2_eq in H4. simpl_Forall. eapply Forall2_trans_ex in H4; [|eauto].
          simpl_Forall. inv_equalities. auto.
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
    Qed.

    Fact iface_incl_wt_block : forall d Γ,
        wt_block G1 Γ d ->
        wt_block G2 Γ d.
    Proof.
      induction d using block_ind2; intros * Hwt; inv Hwt.
      - constructor; auto using iface_incl_wt_equation.
      - econstructor; eauto using iface_incl_wt_exp.
      - constructor; auto using iface_incl_wt_exp.
        rewrite Forall_forall in *; eauto.
      - econstructor; eauto using iface_incl_wt_exp.
        + apply Heq; auto.
        + simpl_Forall. take (wt_branch _ _) and inv it. constructor.
          simpl_Forall; eauto.
      - econstructor; eauto; simpl_Forall; eauto using iface_incl_wt_exp, iface_incl_wt_clock.
        take (wt_branch _ _) and inv it. destruct_conjs. constructor.
        split; auto. destruct s; destruct_conjs.
        eapply iface_incl_wt_scope; eauto.
        intros ? (?&?); split; simpl_Forall; eauto using iface_incl_wt_exp.
      - econstructor; eauto; simpl_Forall; eauto using iface_incl_wt_exp, iface_incl_wt_clock.
        take (wt_branch _ _) and inv it. destruct_conjs. constructor.
        split; simpl_Forall; eauto using iface_incl_wt_exp.
        destruct s; destruct_conjs.
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
    intros * Hincl Hwt. inv Hwt.
    repeat split.
    1-3:unfold wt_clocks in *; simpl_Forall; eauto using iface_incl_wt_clock, iface_incl_wt_type.
    - eauto using iface_incl_wt_block.
  Qed.

  Global Hint Resolve iface_incl_wt_type iface_incl_wt_clock
         iface_incl_wt_exp iface_incl_wt_equation iface_incl_wt_block : ltyping.

  (** *** wt implies wl *)

  Local Hint Constructors wl_exp wl_block : ltyping.

  Fact wt_exp_wl_exp {PSyn prefs} : forall (G: @global PSyn prefs) Γ e,
      wt_exp G Γ e ->
      wl_exp G e.
  Proof with eauto.
    induction e using exp_ind2; intro Hwt; inv Hwt; simpl in *; auto with ltyping;
      econstructor; eauto;
      repeat match goal with
             | |- context [numstreams _] => rewrite <-length_typeof_numstreams
             | H:typeof ?e = _ |- context [typeof ?e] => rewrite H
             | H:typesof ?e = _ |- context [typesof ?e] => rewrite H
             | |- context [length (annots ?es)] =>
                 erewrite <-map_length, <-typesof_annots
             | |- context [length (map _ _)] => rewrite map_length
             | H:None = Some _ |- _ => inv H
             | H:Some _ = Some _ |- _ => inv H
             | _ => simpl_Forall; intros
             end; simpl; auto.
    all:repeat take (Forall2 _ _ _) and apply Forall2_length in it; auto; clear it.
    take (typesof es <> []) and idtac. contradict it.
    rewrite typesof_annots, it; auto.
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
    intros * Hp Hwt. inv Hwt; subst Γ'.
    constructor; eauto.
  Qed.

  Fact wt_block_wl_block {PSyn prefs} : forall (G: @global PSyn prefs) d Γ,
      wt_block G Γ d ->
      wl_block G d.
  Proof.
    induction d using block_ind2; intros * Wt; inv Wt; eauto with ltyping.
    - econstructor; eauto with ltyping.
      rewrite <-length_typeof_numstreams, H5; auto.
    - econstructor; eauto with ltyping.
      + simpl_Forall; eauto.
      + now rewrite <-length_typeof_numstreams, H5.
    - econstructor; eauto with ltyping.
      + rewrite <-length_typeof_numstreams, H3; auto.
      + simpl_Forall; eauto.
        take (wt_branch _ _) and inv it. constructor. simpl_Forall; eauto.
    - econstructor; simpl_Forall; eauto.
      + split; eauto with ltyping. now rewrite <-length_typeof_numstreams, H2.
      + take (wt_branch _ _) and inv it. destruct_conjs. constructor.
        subst; split; simpl; auto.
        destruct s; destruct_conjs. eapply wt_scope_wl_scope; eauto.
        intros * (?&?); split; simpl_Forall; eauto.
        split; eauto with ltyping. now rewrite <-length_typeof_numstreams, H11.
    - econstructor; simpl_Forall; eauto.
      take (wt_branch _ _) and inv it. destruct_conjs. constructor. split; simpl_Forall.
      + split; eauto with ltyping. now rewrite <-length_typeof_numstreams, H6.
      + destruct s; destruct_conjs. eapply wt_scope_wl_scope; eauto.
        intros * (?&?); simpl in *; subst; split; auto. simpl_Forall; eauto.
    - constructor. eapply wt_scope_wl_scope; eauto.
      intros; simpl_Forall; eauto.
  Qed.
  Global Hint Resolve wt_block_wl_block : ltyping.

  Fact wt_node_wl_node {PSyn prefs} : forall (G: @global PSyn prefs) n,
      wt_node G n ->
      wl_node G n.
  Proof with eauto with ltyping.
    intros G n Wt. inv Wt.
    econstructor...
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

  (** *** If an expression is well-typed, all the types appearing inside are well-typed *)
  Section wt_type.
    Context {PSyn : list decl -> block -> Prop}.
    Context {prefs : PS.t}.
    Variable G : @global PSyn prefs.

    Hypothesis HwtG : wt_global G.

    Lemma wt_exp_wt_type : forall Γ e,
        Forall (wt_type G.(types)) (map (fun '(_, e) => e.(typ)) Γ) ->
        wt_exp G Γ e ->
        Forall (wt_type G.(types)) (typeof e).
    Proof.
      induction e using exp_ind2; intros * Hvars Hwt; inv Hwt; simpl.
      - (* const *)
        repeat constructor.
      - (* enum *)
        repeat (constructor; auto).
      - (* var *)
        repeat constructor. inv H1. simpl_Forall; auto.
      - (* last *)
        repeat constructor. inv H1. simpl_Forall; auto.
      - (* unop *) constructor; auto.
      - (* binop *) constructor; auto.
      - (* extern *) repeat constructor; auto.
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
        eapply wt_find_node in H7 as (?&Hwtn&Heq); eauto. inv Hwtn; subst Γ0.
        take (Forall _ (_ ++ _)) and apply Forall_app in it as (?&?).
        eapply Forall2_ignore2 in H9. autounfold with list in *. simpl_Forall. subst.
        rewrite <-Heq; auto.
    Qed.

    Corollary wt_exps_wt_type : forall Γ es,
        Forall (wt_type G.(types)) (map (fun '(_, e) => e.(typ)) Γ) ->
        Forall (wt_exp G Γ) es ->
        Forall (wt_type G.(types)) (typesof es).
    Proof.
      unfold typesof; induction es;
        intros * Hen1 Hwt; inv Hwt; simpl; auto.
      apply Forall_app; split; auto.
      eapply wt_exp_wt_type in H1; eauto.
    Qed.

  End wt_type.

  (** ** wc implies wx *)

  Global Hint Constructors wx_exp wl_block : ltyping.

  Lemma wt_clock_wx_clock : forall types vars ck,
      wt_clock types vars ck ->
      wx_clock vars ck.
  Proof.
    induction ck; intros * Hwt; inv Hwt; constructor; eauto.
    inv H2. econstructor; eauto using In_InMembers.
  Qed.

  Fact wt_exp_wx_exp {PSyn prefs} (G: @global PSyn prefs) : forall Γ e,
      wt_exp G Γ e ->
      wx_exp Γ e.
  Proof with eauto with ltyping senv.
    induction e using exp_ind2; intro Hwt; inv Hwt; econstructor;
      repeat match goal with
             | H: None = Some _ |- _ => inv H
             | H: Some _ = Some _ |- _ => inv H
             | _ => simpl_Forall; intros; subst
             end; eauto with senv lclocking.
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
  Qed.

  Fact wt_block_wx_block {PSyn prefs} (G: @global PSyn prefs) : forall blk Γ,
      wt_block G Γ blk ->
      wx_block Γ blk.
  Proof.
    induction blk using block_ind2; intros * Wt; inv Wt; eauto with ltyping.
    all:econstructor; simpl_Forall; eauto with ltyping.
    - take (wt_branch _ _) and inv it. constructor. simpl_Forall; eauto.
    - take (wt_branch _ _) and inv it. destruct_conjs. constructor.
      destruct s; destruct_conjs. subst; split; auto.
      eapply wt_scope_wx_scope; eauto.
      intros * (?&?); split; simpl_Forall; eauto with ltyping.
    -  take (wt_branch _ _) and inv it. destruct_conjs. constructor.
      split; simpl_Forall; eauto with ltyping.
      destruct s; destruct_conjs.
      eapply wt_scope_wx_scope; eauto.
      intros * (?&?); simpl in *; subst; split; auto; simpl_Forall; eauto with ltyping.
    - eapply wt_scope_wx_scope; eauto.
      intros; simpl_Forall; eauto with ltyping.
  Qed.
  Global Hint Resolve wt_block_wx_block : ltyping.

  Fact wt_node_wx_node {PSyn prefs} : forall (G: @global PSyn prefs) n,
      wt_node G n ->
      wx_node n.
  Proof.
    intros G n Wt. inv Wt; subst Γ.
    econstructor; eauto with ltyping.
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

  Lemma wt_clock_Is_free_in : forall x types env ck,
      wt_clock types env ck ->
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
