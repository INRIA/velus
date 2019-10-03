From Velus Require Import Common.
From Velus Require Import Operators.
From Velus Require Import Clocks.
From Velus Require Import Lustre.LSyntax.

From Coq Require Import List.
Import List.ListNotations.
Open Scope list_scope.

From Coq Require Import Morphisms.

(** * Lustre typing *)

(**

  Typing judgements for Lustre.
  Classify Lustre programs which are statically well-formed.

 *)

Module Type LTYPING
       (Import Ids  : IDS)
       (Import Op   : OPERATORS)
       (Import Syn  : LSYNTAX Ids Op).

  Section WellTyped.

    Variable G    : global.
    Variable vars : list (ident * type).

    Inductive wt_clock : clock -> Prop :=
    | wt_Cbase:
        wt_clock Cbase
    | wt_Con: forall ck x b,
        In (x, bool_type) vars ->
        wt_clock ck ->
        wt_clock (Con ck x b).

    Inductive wt_nclock : nclock -> Prop :=
    | wt_Cnamed: forall id ck,
        wt_clock ck ->
        wt_nclock (ck, id).

    Inductive wt_exp : exp -> Prop :=
    | wt_Econst: forall c,
        wt_exp (Econst c)

    | wt_Evar: forall x ty nck,
        In (x, ty) vars ->
        wt_nclock nck ->
        wt_exp (Evar x (ty, nck))

    | wt_Eunop: forall op e tye ty nck,
        wt_exp e ->
        typeof e = [tye] ->
        type_unop op tye = Some ty ->
        wt_nclock nck ->
        wt_exp (Eunop op e (ty, nck))

    | wt_Ebinop: forall op e1 e2 ty1 ty2 ty nck,
        wt_exp e1 ->
        wt_exp e2 ->
        typeof e1 = [ty1] ->
        typeof e2 = [ty2] ->
        type_binop op ty1 ty2 = Some ty ->
        wt_nclock nck ->
        wt_exp (Ebinop op e1 e2 (ty, nck))

    | wt_Efby: forall e0s es anns,
        Forall wt_exp e0s ->
        Forall wt_exp es ->
        typesof es = map fst anns ->
        typesof e0s = map fst anns ->
        Forall wt_nclock (map snd anns) ->
        wt_exp (Efby e0s es anns)

    | wt_Ewhen: forall es x b tys nck,
        Forall wt_exp es ->
        typesof es = tys ->
        In (x, bool_type) vars ->
        wt_nclock nck ->
        wt_exp (Ewhen es x b (tys, nck))

    | wt_Emerge: forall x ets efs tys nck,
        Forall wt_exp ets ->
        Forall wt_exp efs ->
        In (x, bool_type) vars ->
        typesof ets = tys ->
        typesof efs = tys ->
        wt_nclock nck ->
        wt_exp (Emerge x ets efs (tys, nck))

    | wt_Eifte: forall e ets efs tys nck,
        wt_exp e ->
        Forall wt_exp ets ->
        Forall wt_exp efs ->
        typeof e = [bool_type] ->
        typesof ets = tys ->
        typesof efs = tys ->
        wt_nclock nck ->
        wt_exp (Eite e ets efs (tys, nck))

    | wt_Eapp: forall f es anns n,
        Forall wt_exp es ->
        find_node f G = Some n ->
        Forall2 (fun et '(_, (t, _)) => et = t) (typesof es) n.(n_in) ->
        Forall2 (fun a '(_, (t, _)) => fst a = t) anns n.(n_out) ->
        Forall (fun a => wt_nclock (snd a)) anns ->
        wt_exp (Eapp f es None anns)

    | wt_EappReset: forall f es r anns n,
        Forall wt_exp es ->
        find_node f G = Some n ->
        Forall2 (fun et '(_, (t, _)) => et = t) (typesof es) n.(n_in) ->
        Forall2 (fun a '(_, (t, _)) => fst a = t) anns n.(n_out) ->
        Forall (fun a => wt_nclock (snd a)) anns ->
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
          wt_nclock nck ->
          P (Evar x (ty, nck)).

      Hypothesis EunopCase:
        forall op e tye ty nck,
          wt_exp e ->
          P e ->
          typeof e = [tye] ->
          type_unop op tye = Some ty ->
          wt_nclock nck ->
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
          wt_nclock nck ->
          P (Ebinop op e1 e2 (ty, nck)).

      Hypothesis EfbyCase:
        forall e0s es anns,
          Forall wt_exp e0s ->
          Forall wt_exp es ->
          Forall P e0s ->
          Forall P es ->
          typesof es = map fst anns ->
          typesof e0s = map fst anns ->
          Forall wt_nclock (map snd anns) ->
          P (Efby e0s es anns).

      Hypothesis EwhenCase:
        forall es x b tys nck,
          Forall wt_exp es ->
          Forall P es ->
          typesof es = tys ->
          In (x, bool_type) vars ->
          wt_nclock nck ->
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
          wt_nclock nck ->
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
          wt_nclock nck ->
          P (Eite e ets efs (tys, nck)).

      Hypothesis EappCase:
        forall f es anns n,
          Forall wt_exp es ->
          Forall P es ->
          find_node f G = Some n ->
          Forall2 (fun et '(_, (t, _)) => et = t) (typesof es) n.(n_in) ->
          Forall2 (fun a '(_, (t, _)) => fst a = t) anns n.(n_out) ->
          Forall (fun a => wt_nclock (snd a)) anns ->
          P (Eapp f es None anns).

      Hypothesis EappResetCase:
        forall f es r anns n,
          Forall wt_exp es ->
          Forall P es ->
          find_node f G = Some n ->
          Forall2 (fun et '(_, (t, _)) => et = t) (typesof es) n.(n_in) ->
          Forall2 (fun a '(_, (t, _)) => fst a = t) anns n.(n_out) ->
          Forall (fun a => wt_nclock (snd a)) anns ->
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
          clear H1. induction H; eauto.
        - eapply EappResetCase; eauto.
          clear H1. induction H; eauto.
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
       /\ Forall (wt_equation G (idty (n.(n_in) ++ n.(n_vars) ++ n.(n_out))))
                 n.(n_eqs).

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
          | H:Forall (fun a => wt_nclock env' (snd a)) _ |- _ =>
            setoid_rewrite Henv in H
          | H:Forall (fun a => wt_nclock env (snd a)) _ |- _ =>
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

  Lemma wt_exp_clockof:
    forall G env e,
      wt_exp G env e ->
      Forall (wt_clock env) (clockof e).
  Proof.
    intros * Hwt.
    apply Forall_forall. intros ck Hin.
    inv Hwt; simpl in *.
    - destruct Hin as [Hin|]; [|contradiction].
      rewrite <-Hin; auto with ltyping.
    - destruct Hin as [Hin|]; [|contradiction].
      rewrite <-Hin.
      destruct nck; unfold ckstream; simpl in *;
        match goal with H:wt_nclock _ _ |- _ => inv H end; auto.
    - destruct Hin as [Hin|]; [|contradiction].
      rewrite <-Hin.
      destruct nck; unfold ckstream; simpl in *;
        match goal with H:wt_nclock _ _ |- _ => inv H end; auto.
    - destruct Hin as [Hin|]; [|contradiction].
      rewrite <-Hin.
      destruct nck; unfold ckstream; simpl in *;
        match goal with H:wt_nclock _ _ |- _ => inv H end; auto.
    - match goal with H:Forall (wt_nclock _) _ |- _ =>
                      rewrite Forall_map in H end.
      apply in_map_iff in Hin.
      destruct Hin as ((ty & nck) & Hck & Hin).
      apply Forall_forall with (1:=H3) in Hin.
      destruct nck; unfold ckstream in *; simpl in *; subst;
        match goal with H:wt_nclock _ _ |- _ => inv H end; auto.
    - destruct nck; unfold ckstream in *; simpl in *;
        apply in_map_iff in Hin; destruct Hin as (? & Hs & Hin); subst;
          match goal with H:wt_nclock _ _ |- _ => inv H end; auto.
    - destruct nck; unfold ckstream in *; simpl in *;
        apply in_map_iff in Hin; destruct Hin as (? & Hs & Hin); subst;
          match goal with H:wt_nclock _ _ |- _ => inv H end; auto.
    - destruct nck; unfold ckstream in *; simpl in *;
        apply in_map_iff in Hin; destruct Hin as (? & Hs & Hin); subst;
          match goal with H:wt_nclock _ _ |- _ => inv H end; auto.
    - apply in_map_iff in Hin.
      destruct Hin as (x & Hs & Hin).
      match goal with H:Forall _ anns |- _ =>
                      apply Forall_forall with (1:=H) in Hin end.
      destruct x as (ty, nck).
      destruct nck; unfold ckstream in *; simpl in *;
        subst; match goal with H:wt_nclock _ _ |- _ => inv H end; auto.
    - apply in_map_iff in Hin.
      destruct Hin as (x & Hs & Hin).
      match goal with H:Forall _ anns |- _ =>
                      apply Forall_forall with (1:=H) in Hin end.
      destruct x as (ty, nck).
      destruct nck; unfold ckstream in *; simpl in *;
        subst; match goal with H:wt_nclock _ _ |- _ => inv H end; auto.
  Qed.

End LTYPING.

Module LTypingFun
       (Ids  : IDS)
       (Op   : OPERATORS)
       (Syn  : LSYNTAX Ids Op)
       <: LTYPING Ids Op Syn.
  Include LTYPING Ids Op Syn.
End LTypingFun.
