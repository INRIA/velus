From Velus Require Import Common.
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
       (Import Ids  : IDS)
       (Import Op   : OPERATORS)
       (Import Syn  : LSYNTAX Ids Op).

  Inductive wt_clock : list (ident * type) -> clock -> Prop :=
  | wt_Cbase: forall vars,
      wt_clock vars Cbase
  | wt_Con: forall vars ck x b,
      In (x, bool_type) vars ->
      wt_clock vars ck ->
      wt_clock vars (Con ck x b).

  Inductive wt_nclock : list (ident * type) -> nclock -> Prop :=
  | wt_Cnamed: forall vars id ck,
      wt_clock vars ck ->
      wt_nclock vars (ck, id).

  Section WellTyped.

    Variable G    : global.
    Variable vars : list (ident * type).

    Inductive wt_exp : exp -> Prop :=
    | wt_Econst: forall c,
        wt_exp (Econst c)

    | wt_Evar: forall x ty nck,
        In (x, ty) vars ->
        wt_nclock vars nck ->
        wt_exp (Evar x (ty, nck))

    | wt_Eunop: forall op e tye ty nck,
        wt_exp e ->
        typeof e = [tye] ->
        type_unop op tye = Some ty ->
        wt_nclock vars nck ->
        wt_exp (Eunop op e (ty, nck))

    | wt_Ebinop: forall op e1 e2 ty1 ty2 ty nck,
        wt_exp e1 ->
        wt_exp e2 ->
        typeof e1 = [ty1] ->
        typeof e2 = [ty2] ->
        type_binop op ty1 ty2 = Some ty ->
        wt_nclock vars nck ->
        wt_exp (Ebinop op e1 e2 (ty, nck))

    | wt_Efby: forall e0s es anns,
        Forall wt_exp e0s ->
        Forall wt_exp es ->
        typesof es = map fst anns ->
        typesof e0s = map fst anns ->
        Forall (wt_nclock vars) (map snd anns) ->
        wt_exp (Efby e0s es anns)

    | wt_Ewhen: forall es x b tys nck,
        Forall wt_exp es ->
        typesof es = tys ->
        In (x, bool_type) vars ->
        wt_nclock vars nck ->
        wt_exp (Ewhen es x b (tys, nck))

    | wt_Emerge: forall x ets efs tys nck,
        Forall wt_exp ets ->
        Forall wt_exp efs ->
        In (x, bool_type) vars ->
        typesof ets = tys ->
        typesof efs = tys ->
        wt_nclock vars nck ->
        wt_exp (Emerge x ets efs (tys, nck))

    | wt_Eifte: forall e ets efs tys nck,
        wt_exp e ->
        Forall wt_exp ets ->
        Forall wt_exp efs ->
        typeof e = [bool_type] ->
        typesof ets = tys ->
        typesof efs = tys ->
        wt_nclock vars nck ->
        wt_exp (Eite e ets efs (tys, nck))

    | wt_Eapp: forall f es anns n,
        Forall wt_exp es ->
        find_node f G = Some n ->
        Forall2 (fun et '(_, (t, _)) => et = t) (typesof es) n.(n_in) ->
        Forall2 (fun a '(_, (t, _)) => fst a = t) anns n.(n_out) ->
        Forall (fun a => wt_nclock (vars++(idty (fresh_ins es++anon_streams anns))) (snd a)) anns ->
        wt_exp (Eapp f es None anns)

    | wt_EappReset: forall f es r anns n,
        Forall wt_exp es ->
        find_node f G = Some n ->
        Forall2 (fun et '(_, (t, _)) => et = t) (typesof es) n.(n_in) ->
        Forall2 (fun a '(_, (t, _)) => fst a = t) anns n.(n_out) ->
        Forall (fun a => wt_nclock (vars++(idty (fresh_ins es++anon_streams anns))) (snd a)) anns ->
        wt_exp r ->
        typeof r = [bool_type] ->
        wt_exp (Eapp f es (Some r) anns).

    Section wt_exp_ind2.

      Variable P : exp -> Prop.

      Hypothesis EconstCase:
        forall c : const,
          P (Econst c).

      Hypothesis EvarCase:
        forall x ty nck,
          In (x, ty) vars ->
          wt_nclock vars nck ->
          P (Evar x (ty, nck)).

      Hypothesis EunopCase:
        forall op e tye ty nck,
          wt_exp e ->
          P e ->
          typeof e = [tye] ->
          type_unop op tye = Some ty ->
          wt_nclock vars nck ->
          P (Eunop op e (ty, nck)).

      Hypothesis EbinopCase:
        forall op e1 e2 ty1 ty2 ty nck,
          wt_exp e1 ->
          P e1 ->
          wt_exp e2 ->
          P e2 ->
          typeof e1 = [ty1] ->
          typeof e2 = [ty2] ->
          type_binop op ty1 ty2 = Some ty ->
          wt_nclock vars nck ->
          P (Ebinop op e1 e2 (ty, nck)).

      Hypothesis EfbyCase:
        forall e0s es anns,
          Forall wt_exp e0s ->
          Forall wt_exp es ->
          Forall P e0s ->
          Forall P es ->
          typesof es = map fst anns ->
          typesof e0s = map fst anns ->
          Forall (wt_nclock vars) (map snd anns) ->
          P (Efby e0s es anns).

      Hypothesis EwhenCase:
        forall es x b tys nck,
          Forall wt_exp es ->
          Forall P es ->
          typesof es = tys ->
          In (x, bool_type) vars ->
          wt_nclock vars nck ->
          P (Ewhen es x b (tys, nck)).

      Hypothesis EmergeCase:
        forall x ets efs tys nck,
          Forall wt_exp ets ->
          Forall P ets ->
          Forall wt_exp efs ->
          Forall P efs ->
          In (x, bool_type) vars ->
          typesof ets = tys ->
          typesof efs = tys ->
          wt_nclock vars nck ->
          P (Emerge x ets efs (tys, nck)).

      Hypothesis EiteCase:
        forall e ets efs tys nck,
          wt_exp e ->
          P e ->
          Forall wt_exp ets ->
          Forall P ets ->
          Forall wt_exp efs ->
          Forall P efs ->
          typeof e = [bool_type] ->
          typesof ets = tys ->
          typesof efs = tys ->
          wt_nclock vars nck ->
          P (Eite e ets efs (tys, nck)).

      Hypothesis EappCase:
        forall f es anns n,
          Forall wt_exp es ->
          Forall P es ->
          find_node f G = Some n ->
          Forall2 (fun et '(_, (t, _)) => et = t) (typesof es) n.(n_in) ->
          Forall2 (fun a '(_, (t, _)) => fst a = t) anns n.(n_out) ->
          Forall (fun a => wt_nclock (vars++(idty (fresh_ins es++anon_streams anns))) (snd a)) anns ->
          P (Eapp f es None anns).

      Hypothesis EappResetCase:
        forall f es r anns n,
          Forall wt_exp es ->
          Forall P es ->
          find_node f G = Some n ->
          Forall2 (fun et '(_, (t, _)) => et = t) (typesof es) n.(n_in) ->
          Forall2 (fun a '(_, (t, _)) => fst a = t) anns n.(n_out) ->
          Forall (fun a => wt_nclock (vars++(idty (fresh_ins es++anon_streams anns))) (snd a)) anns ->
          wt_exp r ->
          P r ->
          typeof r = [bool_type] ->
          P (Eapp f es (Some r) anns).

      Fixpoint wt_exp_ind2 (e: exp) (H: wt_exp e) {struct H} : P e.
      Proof.
        destruct H; eauto.
        - apply EfbyCase; auto.
          + clear H2. induction H; auto.
          + clear H1. induction H0; auto.
        - apply EwhenCase; auto.
          clear H0. induction H; auto.
        - apply EmergeCase; auto.
          clear H2. induction H; auto.
          clear H3. induction H0; auto.
        - apply EiteCase; auto.
          clear H3. induction H0; auto.
          clear H4. induction H1; auto.
        - eapply EappCase; eauto.
          clear H1 H3. induction H; eauto.
        - eapply EappResetCase; eauto.
          clear H1 H3. induction H; eauto.
      Qed.

    End wt_exp_ind2.

    Definition wt_equation (eq : equation) : Prop :=
      let (xs, es) := eq in
      Forall wt_exp es
      /\ Forall2 (fun x ty=> In (x, ty) vars) xs (typesof es).

  End WellTyped.

  Definition wt_clocks (vars: list (ident * (type * clock)))
                           : list (ident * (type * clock)) -> Prop :=
    Forall (fun '(_, (_, ck)) => wt_clock (idty vars) ck).

  Definition wt_node (G: global) (n: node) : Prop
    :=    wt_clocks n.(n_in) n.(n_in)
       /\ wt_clocks (n.(n_in) ++ n.(n_out)) n.(n_out)
       /\ wt_clocks (n.(n_in) ++ n.(n_out) ++ n.(n_vars)) n.(n_vars)
       /\ Forall (wt_equation G (idty (n.(n_in) ++ n.(n_vars) ++ n.(n_out)))) n.(n_eqs).

  Inductive wt_global : global -> Prop :=
  | wtg_nil:
      wt_global []
  | wtg_cons: forall n ns,
      wt_global ns ->
      wt_node ns n ->
      Forall (fun n'=> n.(n_name) <> n'.(n_name) :> ident) ns ->
      wt_global (n::ns).

  Hint Constructors wt_clock wt_nclock wt_exp wt_global : ltyping.
  Hint Unfold wt_equation : ltyping.

  Lemma wt_global_NoDup:
    forall g,
      wt_global g ->
      NoDup (map n_name g).
  Proof.
    induction g; eauto using NoDup.
    intro WTg. simpl. constructor.
    2:apply IHg; now inv WTg.
    intro Hin.
    inversion_clear WTg as [|? ? ? WTn Hn].
    change (Forall (fun n' => (fun i=> a.(n_name) <> i) n'.(n_name)) g)%type in Hn.
    apply Forall_map in Hn.
    apply Forall_forall with (1:=Hn) in Hin.
    now contradiction Hin.
  Qed.

  Lemma wt_global_app:
    forall G G',
      wt_global (G' ++ G) ->
      wt_global G.
  Proof.
    induction G'; auto.
    simpl. intro Hwt.
    inversion Hwt; auto.
  Qed.

  Lemma wt_find_node:
    forall G f n,
      wt_global G ->
      find_node f G = Some n ->
      exists G', wt_node G' n.
  Proof.
    intros G f n' Hwt Hfind.
    apply find_node_split in Hfind.
    destruct Hfind as (bG & aG & HG).
    subst. apply wt_global_app in Hwt.
    inversion Hwt. eauto.
  Qed.

  Lemma wt_clock_add:
    forall x v env ck,
      ~InMembers x env ->
      wt_clock env ck ->
      wt_clock ((x, v) :: env) ck.
  Proof.
    induction ck; auto with ltyping.
    inversion 2.
    auto with ltyping datatypes.
  Qed.

  Instance wt_clock_Proper:
    Proper (@Permutation.Permutation (ident * type) ==> @eq clock ==> iff)
           wt_clock.
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

  Instance wt_nclock_Proper:
    Proper (@Permutation.Permutation (ident * type) ==> @eq nclock ==> iff)
           wt_nclock.
  Proof.
    intros env' env Henv ck' ck Hck.
    rewrite Hck; clear Hck ck'.
    destruct ck;
      split; inversion 1;
        (rewrite Henv in * || rewrite <-Henv in * || idtac);
        auto with ltyping.
  Qed.

  Instance wt_nclock_pointwise_Proper:
    Proper (@Permutation.Permutation (ident * type)
                          ==> pointwise_relation nclock iff) wt_nclock.
  Proof.
    intros env' env Henv e.
    now rewrite Henv.
  Qed.

  Instance wt_exp_Proper:
    Proper (@eq global ==> @Permutation.Permutation (ident * type)
                ==> @eq exp ==> iff)
           wt_exp.
  Proof.
    intros G G' HG env' env Henv e' e He.
    rewrite HG, He. clear HG He.
    split; intro H;
      induction H using wt_exp_ind2;
      (rewrite Henv in * || rewrite <-Henv in * || idtac);
      try match goal with
          | H:Forall (fun a => wt_nclock (env' ++ _) (snd a)) _ |- _ =>
            setoid_rewrite Henv in H
          | H:Forall (fun a => wt_nclock (env ++ _) (snd a)) _ |- _ =>
            setoid_rewrite <-Henv in H
          end;
      eauto with ltyping;
      econstructor; eauto.
  Qed.

  Instance wt_exp_pointwise_Proper:
    Proper (@eq global ==> @Permutation.Permutation (ident * type)
                                     ==> pointwise_relation exp iff) wt_exp.
  Proof.
    intros G G' HG env' env Henv e.
    now rewrite HG, Henv.
  Qed.

  Instance wt_equation_Proper:
    Proper (@eq global ==> @Permutation.Permutation (ident * type)
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

    Fact wt_clock_incl : forall vars vars' cl,
      incl vars vars' ->
      wt_clock vars cl ->
      wt_clock vars' cl.
    Proof.
      intros vars vars' cl Hincl Hwt.
      induction Hwt.
      - constructor.
      - constructor; auto.
    Qed.
    Local Hint Resolve wt_clock_incl.

    Fact wt_nclock_incl : forall vars vars' cl,
        incl vars vars' ->
        wt_nclock vars cl ->
        wt_nclock vars' cl.
    Proof.
      intros vars vars' cl Hincl Hwt.
      destruct Hwt; constructor; eauto.
    Qed.
    Local Hint Resolve wt_nclock_incl.

    Lemma wt_exp_incl : forall G vars vars' e,
        incl vars vars' ->
        wt_exp G vars e ->
        wt_exp G vars' e.
    Proof.
      intros G vars vars' e Hincl Hwt.
      induction Hwt using wt_exp_ind2;
        econstructor; eauto.
      - (* fby *)
        eapply Forall_impl; [| eauto].
        intros; eauto.
      - (* app *)
        eapply Forall_impl; [| eauto].
        intros; simpl in *; eauto.
        eapply wt_nclock_incl; eauto.
        eapply incl_appl'; eauto.
      - (* app (reset) *)
        eapply Forall_impl; [| eauto].
        intros; simpl in *; eauto.
        eapply wt_nclock_incl; eauto.
        eapply incl_appl'; eauto.
    Qed.

    Lemma wt_equation_incl : forall G vars vars' eq,
        incl vars vars' ->
        wt_equation G vars eq ->
        wt_equation G vars' eq.
    Proof.
      intros G vars vars' eq Hincl Hwt.
      destruct eq; simpl in *. destruct Hwt as [Hwt1 Hwt2].
      split.
      - eapply Forall_impl; [| eauto].
        intros. eapply wt_exp_incl; eauto.
      - eapply Forall2_impl_In; [| eauto].
        intros; simpl in H1. eauto.
    Qed.

  End incl.

  Local Hint Resolve wt_clock_incl incl_appl incl_refl.
  Lemma wt_exp_clockof:
    forall G env e,
      wt_exp G env e ->
      Forall (wt_clock (env++idty (fresh_in e))) (clockof e).
  Proof.
    intros * Hwt.
    apply Forall_forall. intros ck Hin.
    inv Hwt; simpl in *.
    - destruct Hin as [Hin|]; [|contradiction].
      rewrite <-Hin; auto with ltyping.
    - destruct Hin as [Hin|]; [|contradiction].
      rewrite <-Hin.
      destruct nck; unfold clock_of_nclock; simpl in *;
        match goal with H:wt_nclock _ _ |- _ => inv H end.
      rewrite app_nil_r; auto.
    - destruct Hin as [Hin|]; [|contradiction].
      rewrite <-Hin.
      destruct nck; unfold clock_of_nclock; simpl in *;
        match goal with H:wt_nclock _ _ |- _ => inv H end; eauto.
    - destruct Hin as [Hin|]; [|contradiction].
      rewrite <-Hin.
      destruct nck; unfold clock_of_nclock; simpl in *;
        match goal with H:wt_nclock _ _ |- _ => inv H end; eauto.
    - match goal with H:Forall (wt_nclock _) _ |- _ =>
                      rewrite Forall_map in H end.
      apply in_map_iff in Hin.
      destruct Hin as ((ty & nck) & Hck & Hin).
      apply Forall_forall with (1:=H3) in Hin.
      destruct nck; unfold clock_of_nclock in *; simpl in *; subst;
        match goal with H:wt_nclock _ _ |- _ => inv H end; eauto.
    - destruct nck; unfold clock_of_nclock in *; simpl in *;
        apply in_map_iff in Hin; destruct Hin as (? & Hs & Hin); subst;
          match goal with H:wt_nclock _ _ |- _ => inv H end; eauto.
    - destruct nck; unfold clock_of_nclock in *; simpl in *;
        apply in_map_iff in Hin; destruct Hin as (? & Hs & Hin); subst;
          match goal with H:wt_nclock _ _ |- _ => inv H end; eauto.
    - destruct nck; unfold clock_of_nclock in *; simpl in *;
        apply in_map_iff in Hin; destruct Hin as (? & Hs & Hin); subst;
          match goal with H:wt_nclock _ _ |- _ => inv H end; eauto.
    - apply in_map_iff in Hin.
      destruct Hin as (x & Hs & Hin).
      match goal with H:Forall _ anns |- _ =>
                      apply Forall_forall with (1:=H) in Hin end.
      destruct x as (ty, nck).
      destruct nck; unfold clock_of_nclock in *; simpl in *;
        subst; match goal with H:wt_nclock _ _ |- _ => inv H end; eauto.
    - apply in_map_iff in Hin.
      destruct Hin as (x & Hs & Hin).
      match goal with H:Forall _ anns |- _ =>
                      apply Forall_forall with (1:=H) in Hin end.
      destruct x as (ty, nck).
      destruct nck; unfold clock_of_nclock in *; simpl in *;
        subst; match goal with H:wt_nclock _ _ |- _ => inv H end.
      eapply wt_clock_incl; [| eauto].
      eapply incl_appr'. unfold idty; repeat rewrite map_app.
      eapply incl_appr'. eapply incl_appr. reflexivity.
  Qed.

  (** Validation *)

  Module OpAux := OperatorsAux Op.

  Fixpoint check_clock (venv : Env.t type) (ck : clock) : bool :=
    match ck with
    | Cbase => true
    | Con ck' x b =>
      match Env.find x venv with
      | None => false
      | Some xt => (xt ==b bool_type) && check_clock venv ck'
      end
    end.

  Definition check_nclock (venv : Env.t type) (nck : nclock) : bool :=
    check_clock venv (fst nck).

  (* TODO: Move elsewhere? *)
  Local Ltac DestructMatch :=
    repeat progress
           match goal with
           | H:match ?e with _ => _ end = _ |- _ =>
             let Heq := fresh "Heq" in
             destruct e eqn:Heq; try discriminate
           end.

  Lemma check_clock_correct:
    forall venv ck,
      check_clock venv ck = true ->
      wt_clock (Env.elements venv) ck.
  Proof.
    induction ck; intro CC. now constructor.
    simpl in CC. DestructMatch.
    rewrite Bool.andb_true_iff in CC; destruct CC as (CC1 & CC2).
    apply IHck in CC2. rewrite equiv_decb_equiv in CC1; inv CC1.
    apply Env.elements_correct in Heq.
    constructor; auto.
  Qed.

  Lemma check_nclock_correct:
    forall venv nck,
      check_nclock venv nck = true ->
      wt_nclock (Env.elements venv) nck.
  Proof.
    destruct nck as (n, ck).
    intro CC; now apply check_clock_correct in CC.
  Qed.
  Local Hint Resolve check_nclock_correct.

  Section ValidateExpression.

    Variable G : global.
    Variable venv : Env.t type.

    Open Scope option_monad_scope.

    Definition check_paired_types (t1 t2 : type) (tc : ann) : bool :=
      let '(t, c) := tc in
      (t1 ==b t) && (t2 ==b t) && (check_nclock venv c).

    Definition check_reset (rt : option (option (list type))) : bool :=
      match rt with
      | None => true
      | Some (Some [ty]) => ty ==b bool_type
      | _ => false
      end.

    Function check_var (x : ident) (ty : type) : bool :=
      match Env.find x venv with
      | None => false
      | Some xt => ty ==b xt
      end.

    Fixpoint check_exp (e : exp) : option (list type) :=
      match e with
      | Econst c => Some ([type_const c])

      | Evar x (xt, nck) =>
        if check_var x xt && check_nclock venv nck then Some [xt] else None

      | Eunop op e (xt, nck) =>
        do te <- assert_singleton (check_exp e);
        do t <- type_unop op te;
        if (xt ==b t) && check_nclock venv nck then Some [xt] else None

      | Ebinop op e1 e2 (xt, nck) =>
        do te1 <- assert_singleton (check_exp e1);
        do te2 <- assert_singleton (check_exp e2);
        do t <- type_binop op te1 te2;
        if (xt ==b t) && check_nclock venv nck then Some [xt] else None

      | Efby e0s es anns =>
        do t0s <- oconcat (map check_exp e0s);
        do ts <- oconcat (map check_exp es);
        if forall3b check_paired_types t0s ts anns
        then Some (map fst anns) else None

      | Ewhen es x b (tys, nck) =>
        do ts <- oconcat (map check_exp es);
        if check_var x bool_type && (forall2b equiv_decb ts tys) && (check_nclock venv nck)
        then Some tys else None

      | Emerge x e1s e2s (tys, nck) =>
        do t1s <- oconcat (map check_exp e1s);
        do t2s <- oconcat (map check_exp e2s);
        if check_var x bool_type
             && (forall3b equiv_decb3 t1s t2s tys)
             && (check_nclock venv nck)
        then Some tys else None

      | Eite e e1s e2s (tys, nck) =>
        do t1s <- oconcat (map check_exp e1s);
        do t2s <- oconcat (map check_exp e2s);
        do xt <- assert_singleton (check_exp e);
        if (xt ==b bool_type)
             && (forall3b equiv_decb3 t1s t2s tys)
             && (check_nclock venv nck)
        then Some tys else None

      | Eapp f es ro anns =>
        do n <- find_node f G;
        do ts <- oconcat (map check_exp es);
        if (forall2b (fun et '(_, (t, _)) => et ==b t) ts n.(n_in))
             && (forall2b (fun '(ot, oc) '(_, (t, _)) =>
                             check_nclock (Env.adds' (idty (fresh_ins es++anon_streams anns)) venv) oc
                             && (ot ==b t)) anns n.(n_out))
             && check_reset (option_map check_exp ro)
        then Some (map fst anns)
        else None
      end.

    Definition check_rhs (e : exp) : option (list type) :=
      match e with
      | Eapp f es ro anns =>
        do n <- find_node f G;
        do ts <- oconcat (map check_exp es);
        if (forall2b (fun et '(_, (t, _)) => et ==b t) ts n.(n_in))
             && (forall2b (fun '(ot, oc) '(_, (t, _)) =>
                             check_nclock (Env.adds' (idty (fresh_ins es)) venv) oc
                             && (ot ==b t)) anns n.(n_out))
             && check_reset (option_map check_exp ro)
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
      - DestructMatch; simpl.
        rewrite equiv_decb_equiv in HH. inv HH.
        take (Env.find _ _ = Some _) and apply Env.elements_correct in it; eauto.
      - apply Env.elements_complete in HH as ->.
        apply equiv_decb_refl.
    Qed.
    Local Hint Resolve check_var_correct.

    Lemma check_paired_types_correct:
      forall tys1 tys2 anns,
        forall3b check_paired_types tys1 tys2 anns = true ->
        tys1 = map fst anns
        /\ tys2 = map fst anns
        /\ Forall (wt_nclock (Env.elements venv)) (map snd anns).
    Proof.
      setoid_rewrite forall3b_Forall3.
      induction 1 as [|ty1 ty2 (ty, nck) tys1 tys2 anns IH1 IH2 (? & ? & IH3)];
        subst; simpl; eauto.
      simpl in IH1.
      repeat rewrite Bool.andb_true_iff in IH1.
      setoid_rewrite equiv_decb_equiv in IH1.
      destruct IH1 as ((-> & ->) & IH1).
      apply check_nclock_correct in IH1. auto.
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

    Import Permutation.
    Local Hint Constructors wt_exp.
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
               | H:obind _ _ = Some _ |- _ => omonadInv H
               | H:obind2 _ _ = Some _ |- _ => omonadInv H
               | H:obind ?v _ = Some _ |- _ =>
                 let OE:=fresh "OE0" in destruct v eqn:OE; [simpl in H|now omonadInv H]
               | H: _ && _ = true |- _ => apply Bool.andb_true_iff in H as (? & ?)
               | H: ((_ ==b _) = true) |- _ => rewrite equiv_decb_equiv in H; inv H
               | H: check_nclock _ = true |- _ => apply check_nclock_correct in H
               | H: Env.find _ _ = Some _ |- _ => apply Env.elements_correct in H
               | H:(obind2 (Env.find ?x ?env) _) = Some _ |- _ =>
                 let EF := fresh "EF0" in
                 destruct (Env.find x env) eqn:EF
               | H:(if ?c then Some _ else None) = Some _ |- _ =>
                 let C := fresh "C0" in
                 destruct c eqn:C
               | H:None = Some _ |- _ => discriminate
               | H:Some _ = Some _ |- _ => inv H
               | H:assert_singleton _ = Some _ |- _ => apply assert_singleton_spec in H
               | H:check_var _ _ = true |- _ => apply check_var_correct in H
               | H:forall3b check_paired_types ?tys1 ?tys2 ?anns = true |- _ =>
                 apply check_paired_types_correct in H as (? & ? & ?)
               | H:forall2b equiv_decb ?xs ?ys = true |- _ =>
                 apply forall2b_Forall2_equiv_decb in H
               | H:forall3b equiv_decb3 _ _ _ = true |- _ =>
                 apply forall3b_equiv_decb3 in H as (? & ?)
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
        apply oconcat_map_check_exp' in OE1 as (? & ?)...
        subst; eauto using wt_exp.
        + ndup_r ND.
        + ndup_l ND.
      - (* Ewhen *)
        subst. take (Forall _ es) and rewrite Forall_forall in it.
        take (oconcat (map check_exp _) = Some _) and
             apply oconcat_map_check_exp' in it as (? & ?); eauto using wt_exp.
      - (* Emerge *)
        take (Forall _ ets) and rewrite Forall_forall in it.
        take (Forall _ efs) and rewrite Forall_forall in it.
        take (oconcat (map check_exp _) = Some _) and
             apply oconcat_map_check_exp' in it as (? & ?); auto.
        take (oconcat (map check_exp _) = Some _) and
             apply oconcat_map_check_exp' in it as (? & ?); auto.
        subst. eauto using wt_exp.
        + ndup_l ND.
        + ndup_r ND.
      - (* Eite *)
        take (check_exp _ = Some _) and apply IHe in it as (? & ?).
        take (Forall _ ets) and rewrite Forall_forall in it.
        take (Forall _ efs) and rewrite Forall_forall in it.
        take (oconcat (map check_exp _) = Some _) and
             apply oconcat_map_check_exp' in it as (? & ?); auto.
        take (oconcat (map check_exp _) = Some _) and
             apply oconcat_map_check_exp' in it as (? & ?); auto.
        subst. eauto using wt_exp.
        + ndup_simpl.
          rewrite Permutation_swap in ND.
          rewrite app_assoc in ND. apply NoDupMembers_app_l in ND; auto.
        + ndup_simpl.
          rewrite Permutation.Permutation_app_comm in ND.
          repeat rewrite <- app_assoc in ND.
          apply NoDupMembers_app_r in ND. apply NoDupMembers_app_r in ND.
          rewrite Permutation.Permutation_app_comm in ND. assumption.
        + ndup_simpl.
          rewrite app_assoc in ND. apply NoDupMembers_app_l in ND; auto.
      - (* Eapp *)
        take (Forall _ es) and rewrite Forall_forall in it.
        take (oconcat (map check_exp _) = Some _) and
             apply oconcat_map_check_exp' in it as (? & ?); auto.
        2: { destruct ro; ndup_simpl.
             + repeat rewrite app_assoc in ND.
               apply NoDupMembers_app_l in ND. apply NoDupMembers_app_l in ND.
               assumption.
             + rewrite app_assoc in ND.
               apply NoDupMembers_app_l in ND.
               assumption.
        }
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
        assert (Forall (fun ann => wt_nclock ((Env.elements venv)++idty (fresh_ins es++anon_streams a)) (snd ann)) a).
        { repeat take (Forall2 _ _ n.(n_out)) and apply Forall2_ignore2 in it.
          apply Forall_impl_In with (2:=it).
          intros (? & ?) ? ((? & (? & ?)) & (? & EQ)); simpl.
          apply Bool.andb_true_iff in EQ as (EQ1 & EQ2).
          apply check_nclock_correct in EQ1. rewrite Env.elements_adds in EQ1; auto.
          destruct ro; auto.
          ndup_simpl.
          rewrite app_assoc in ND.
          rewrite Permutation_app_comm in ND.
          rewrite <- app_assoc in ND. apply NoDupMembers_app_r in ND.
          rewrite Permutation_app_comm in ND.
          rewrite <- app_assoc in ND; auto.
        }
        destruct ro; econstructor; eauto; simpl in *;
          clear it; DestructMatch; subst;
            destruct (H [t]) as [CE1 CE2]; auto.
        + ndup_simpl.
          repeat rewrite app_assoc in ND.
          apply NoDupMembers_app_l in ND.
          repeat rewrite <- app_assoc in ND.
          rewrite Permutation_swap in ND.
          apply NoDupMembers_app_r in ND; auto.
        + ndup_simpl.
          repeat rewrite app_assoc in ND.
          apply NoDupMembers_app_l in ND.
          repeat rewrite <- app_assoc in ND.
          rewrite Permutation_swap in ND.
          apply NoDupMembers_app_r in ND; auto.
        + rewrite equiv_decb_equiv in H2. congruence.
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

    Lemma check_rhs_correct:
      forall e tys,
        NoDupMembers (Env.elements venv++(idty (anon_in e))) -> (* Should be anon_in ? *)
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
      2: { destruct o; ndup_simpl...
           rewrite app_assoc in ND.
           apply NoDupMembers_app_l in ND... }
      subst.
      assert (Forall2 (fun et '(_, (t, _)) => et = t) (typesof l) n.(n_in)).
        { take (Forall2 _ (typesof l) n.(n_in))
               and apply Forall2_impl_In with (2:=it).
          intros ? (? & (? & ?)) ? ? EQ.
          now rewrite equiv_decb_equiv in EQ. }
        assert (Forall2 (fun ann '(_, (t, _)) => fst ann = t) l0 n.(n_out)).
        { take (Forall2 _ _ n.(n_out)) and apply Forall2_impl_In with (2:=it).
          intros (? & ?) (? & (? & ?)) ? ? EQ.
          apply Bool.andb_true_iff in EQ as (EQ1 & EQ2).
          now rewrite equiv_decb_equiv in EQ2. }
        assert (Forall (fun a => wt_nclock (Env.elements venv ++ idty (fresh_ins l++anon_streams l0)) (snd a)) l0).
        { repeat take (Forall2 _ _ n.(n_out)) and apply Forall2_ignore2 in it.
          apply Forall_impl_In with (2:=it).
          intros (? & ?) ? ((? & (? & ?)) & (? & EQ)); simpl.
          apply Bool.andb_true_iff in EQ as (EQ1 & EQ2).
          unfold idty in *; rewrite map_app in *.
          apply check_nclock_correct in EQ1. rewrite Env.elements_adds in EQ1; auto.
          + eapply wt_nclock_incl; [| eauto]. apply incl_appr'.
            eapply incl_appl. reflexivity.
          + destruct o; auto.
            rewrite map_app in ND. rewrite app_assoc in ND.
            apply NoDupMembers_app_l in ND. assumption. }
        destruct o; simpl in H0; DestructMatch; econstructor...
        1,2:(apply check_exp_correct in Heq as [Hwt Heq]; eauto).
        1,3:unfold idty in *; rewrite map_app in *; rewrite Permutation_swap in ND; apply NoDupMembers_app_r in ND; auto.
        rewrite equiv_decb_equiv in H0. congruence.
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
      DestructMatch.
      take (oconcat (map check_rhs _) = Some _)
           and apply oconcat_map_check_rhs in it as (? & ?).
      take (forall2b check_var _ _ = true)
           and apply forall2b_Forall2 in it.
      setoid_rewrite check_var_correct in it.
      subst; constructor; auto.
      unfold anon_in_eq in ND; auto.
    Qed.

  End ValidateExpression.

  Section interface_eq.

    Hint Constructors wt_exp.
    Fact iface_eq_wt_exp : forall G G' vars e,
        global_iface_eq G G' ->
        wt_exp G vars e ->
        wt_exp G' vars e.
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
        assert (Forall (wt_exp G' vars) es) as Hwt by (rewrite Forall_forall in *; eauto).
        specialize (Heq f).
        remember (find_node f G') as find.
        destruct Heq.
        + congruence.
        + inv H6.
          destruct H1 as [? [? [? ?]]].
          apply wt_Eapp with (n:=sy)...
          * congruence.
          * congruence.
      - (* app (reset) *)
        assert (Forall (wt_exp G' vars) es) as Hwt by (rewrite Forall_forall in *; eauto).
        assert (wt_exp G' vars r) as Hwt' by (rewrite Forall_forall in *; eauto).
        specialize (Heq f).
        remember (find_node f G') as find.
        destruct Heq.
        + congruence.
        + inv H6.
          destruct H1 as [? [? [? ?]]].
          apply wt_EappReset with (n:=sy)...
          * congruence.
          * congruence.
    Qed.

    Fact iface_eq_wt_equation : forall G G' vars equ,
        global_iface_eq G G' ->
        wt_equation G vars equ ->
        wt_equation G' vars equ.
    Proof.
      intros G G' vars [xs es] Heq Hwt.
      simpl in *. destruct Hwt.
      split.
      + rewrite Forall_forall in *. intros x Hin.
        eapply iface_eq_wt_exp; eauto.
      + assumption.
    Qed.

    Lemma iface_eq_wt_node : forall G G' n,
        global_iface_eq G G' ->
        wt_node G n ->
        wt_node G' n.
    Proof.
      intros G G' n Heq Hwt.
      destruct Hwt as [? [? [? Hwt]]].
      repeat split; auto.
      rewrite Forall_forall in *; intros.
      eapply iface_eq_wt_equation; eauto.
    Qed.

  End interface_eq.

  (** ** wt implies wl *)

  Hint Constructors wl_exp.
  Fact wt_exp_wl_exp : forall G vars e,
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
    - (* when *)
      constructor...
      + rewrite Forall_forall in *...
      + rewrite typesof_annots. rewrite map_length...
    - (* merge *)
      constructor...
      + rewrite Forall_forall in *...
      + rewrite Forall_forall in *...
      + rewrite typesof_annots. rewrite map_length...
      + rewrite <- H9, typesof_annots, map_length...
    - (* ite *)
      constructor...
      + rewrite Forall_forall in *...
      + rewrite Forall_forall in *...
      + rewrite <- length_typeof_numstreams, H8...
      + rewrite typesof_annots, map_length...
      + rewrite <- H10, typesof_annots, map_length...
    - (* app *)
      econstructor...
      + rewrite Forall_forall in *...
      + apply Forall2_length in H7. rewrite typesof_annots, map_length in H7...
      + apply Forall2_length in H8...
    - (* app (reset) *)
      econstructor...
      + rewrite Forall_forall in *...
      + rewrite <- length_typeof_numstreams, H11...
      + apply Forall2_length in H7. rewrite typesof_annots, map_length in H7...
      + apply Forall2_length in H8...
  Qed.
  Hint Resolve wt_exp_wl_exp.

  Corollary Forall_wt_exp_wl_exp : forall G vars es,
      Forall (wt_exp G vars) es ->
      Forall (wl_exp G) es.
  Proof. intros. rewrite Forall_forall in *; eauto. Qed.
  Hint Resolve Forall_wt_exp_wl_exp.

  Fact wt_equation_wl_equation : forall G vars equ,
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

  Fact wt_node_wl_node : forall G n,
      wt_node G n ->
      wl_node G n.
  Proof with eauto.
    intros G n [_ [_ [_ Hwt]]].
    unfold wl_node.
    rewrite Forall_forall in *...
  Qed.
  Hint Resolve wt_node_wl_node.

  Fact wt_global_wl_global : forall G,
      wt_global G ->
      wl_global G.
  Proof with eauto.
    intros G Hwt.
    induction Hwt; constructor...
  Qed.
  Hint Resolve wt_global_wl_global.

  (** ** Other useful stuff *)

  Lemma wt_clock_Is_free_in : forall x env ck,
      wt_clock env ck ->
      Is_free_in_clock x ck ->
      InMembers x env.
  Proof.
    induction ck; intros Hwt Hfree;
      inv Hwt; inv Hfree; eauto using In_InMembers.
  Qed.

  Corollary wt_nclock_Is_free_in : forall x env name ck,
      wt_nclock env (ck, name) ->
      Is_free_in_clock x ck ->
      InMembers x env.
  Proof.
    intros * Hwt Hin; inv Hwt. eapply wt_clock_Is_free_in; eauto.
  Qed.

End LTYPING.

Module LTypingFun
       (Ids  : IDS)
       (Op   : OPERATORS)
       (Syn  : LSYNTAX Ids Op)
       <: LTYPING Ids Op Syn.
  Include LTYPING Ids Op Syn.
End LTypingFun.
