Require Import Velus.Common.
Require Import Velus.Operators.
Require Import Velus.Clocks.
Require Import Velus.NLustre.NLExprSyntax.
Require Import Velus.NLustre.NLSyntax.

Require Import List.
Import List.ListNotations.
Open Scope list_scope.

Require Import Morphisms.

(** * NLustre typing *)

(**

  Typing judgements for NLustre and resulting properties.
  Classify NLustre programs which are statically well-formed.

 *)

Module Type NLTYPING
       (Import Ids     : IDS)
       (Import Op      : OPERATORS)
       (Import Clks    : CLOCKS   Ids)
       (Import ExprSyn : NLEXPRSYNTAX Op)
       (Import Syn     : NLSYNTAX Ids Op Clks ExprSyn).

  (** ** Clocks *)

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

    Inductive wt_lexp : lexp -> Prop :=
    | wt_Econst: forall c,
        wt_lexp (Econst c)
    | wt_Evar: forall x ty,
        In (x, ty) vars ->
        wt_lexp (Evar x ty)
    | wt_Ewhen: forall e x b,
        In (x, bool_type) vars ->
        wt_lexp e ->
        wt_lexp (Ewhen e x b)
    | wt_Eunop: forall op e ty,
        type_unop op (typeof e) = Some ty ->
        wt_lexp e ->
        wt_lexp (Eunop op e ty)
    | wt_Ebinop: forall op e1 e2 ty,
        type_binop op (typeof e1) (typeof e2) = Some ty ->
        wt_lexp e1 ->
        wt_lexp e2 ->
        wt_lexp (Ebinop op e1 e2 ty).

    Fixpoint typeofc (ce: cexp): type :=
      match ce with
      | Emerge x t f => typeofc t
      | Eite e t f   => typeofc t
      | Eexp e       => typeof e
      end.

    Inductive wt_cexp : cexp -> Prop :=
    | wt_Emerge: forall x t f,
        In (x, bool_type) vars ->
        typeofc t = typeofc f ->
        wt_cexp t ->
        wt_cexp f ->
        wt_cexp (Emerge x t f)
    | wt_Eite: forall e t f,
        typeof e = bool_type ->
        wt_lexp e ->
        wt_cexp t ->
        wt_cexp f ->
        typeofc t = typeofc f ->
        wt_cexp (Eite e t f)
    | wt_Eexp: forall e,
        wt_lexp e ->
        wt_cexp (Eexp e).

    Inductive wt_equation : equation -> Prop :=
    | wt_EqDef: forall x ck e,
        In (x, typeofc e) vars ->
        wt_clock ck ->
        wt_cexp e ->
        wt_equation (EqDef x ck e)
    | wt_EqApp: forall n xs ck f es,
        find_node f G = Some n ->
        Forall2 (fun x xt => In (x, dty xt) vars) xs n.(n_out) ->
        Forall2 (fun e xt => typeof e = dty xt) es n.(n_in) ->
        wt_clock ck ->
        Forall wt_lexp es ->
        NoDup xs ->
        wt_equation (EqApp xs ck f es None)
    | wt_EqReset: forall n xs ck f es r,
        find_node f G = Some n ->
        Forall2 (fun x xt => In (x, dty xt) vars) xs n.(n_out) ->
        Forall2 (fun e xt => typeof e = dty xt) es n.(n_in) ->
        wt_clock ck ->
        Forall wt_lexp es ->
        NoDup xs ->
        In (r, bool_type) vars ->
        wt_equation (EqApp xs ck f es (Some r))
    | wt_EqFby: forall x ck c0 e,
        In (x, type_const c0) vars ->
        typeof e = type_const c0 ->
        wt_clock ck ->
        wt_lexp e ->
        wt_equation (EqFby x ck c0 e).

  End WellTyped.

  Definition wt_node (G: global) (n: node) : Prop
    := Forall (wt_equation G (idty (n.(n_in) ++ n.(n_vars) ++ n.(n_out))))
              n.(n_eqs).

  (* TODO: replace Welldef_global; except for the Is_well_sch component.
           Notably, typing arguments replace the ~Is_node_in and
           Is_node_in/find_node components. The no duplicate names
           component is replicated exactly. *)
  Inductive wt_global : global -> Prop :=
  | wtg_nil:
      wt_global []
  | wtg_cons: forall n ns,
      wt_global ns ->
      wt_node ns n ->
      Forall (fun n'=> n.(n_name) <> n'.(n_name)) ns ->
      wt_global (n::ns).

  Hint Constructors wt_clock wt_lexp wt_cexp wt_equation wt_global : nltyping.

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
    change (Forall (fun n' => (fun i=> a.(n_name) <> i) n'.(n_name)) g) in Hn.
    apply Forall_map in Hn.
    apply Forall_forall with (1:=Hn) in Hin.
    now contradiction Hin.
  Qed.

  Lemma wt_clock_add:
    forall x v env ck,
      ~InMembers x env ->
      wt_clock env ck ->
      wt_clock ((x, v) :: env) ck.
  Proof.
    induction ck; auto with nltyping.
    inversion 2.
    auto with nltyping datatypes.
  Qed.

  Instance wt_clock_Proper:
    Proper (@Permutation.Permutation (ident * type) ==> @eq clock ==> iff)
           wt_clock.
  Proof.
    intros env' env Henv ck' ck Hck.
    rewrite Hck; clear Hck ck'.
    induction ck.
    - split; auto with nltyping.
    - destruct IHck.
      split; inversion_clear 1; constructor;
        try rewrite Henv in *;
        auto with nltyping.
  Qed.

  Instance wt_lexp_Proper:
    Proper (@Permutation.Permutation (ident * type) ==> @eq lexp ==> iff)
           wt_lexp.
  Proof.
    intros env' env Henv e' e He.
    rewrite He; clear He.
    induction e; try destruct IHe;
      try destruct IHe1, IHe2;
      split; auto with nltyping;
        inversion_clear 1;
        (rewrite Henv in * || rewrite <-Henv in * || idtac);
        auto with nltyping.
  Qed.

  Instance wt_lexp_pointwise_Proper:
    Proper (@Permutation.Permutation (ident * type)
                                     ==> pointwise_relation lexp iff) wt_lexp.
  Proof.
    intros env' env Henv e.
    now rewrite Henv.
  Qed.

  Instance wt_cexp_Proper:
    Proper (@Permutation.Permutation (ident * type) ==> @eq cexp ==> iff)
           wt_cexp.
  Proof.
    intros env' env Henv e' e He.
    rewrite He; clear He.
    induction e; try destruct IHe1, IHe2;
      split; inversion_clear 1; try rewrite Henv in *;
        constructor; auto; now rewrite Henv in *.
  Qed.

  Instance wt_equation_Proper:
    Proper (@eq global ==> @Permutation.Permutation (ident * type)
                ==> @eq equation ==> iff)
           wt_equation.
  Proof.
    intros G1 G2 HG env1 env2 Henv eq1 eq2 Heq.
    rewrite Heq, HG.
    split; intro WTeq.
    - inv WTeq; rewrite Henv in *; eauto with nltyping;
        econstructor; eauto;
          match goal with H:Forall2 _ ?x ?y |- Forall2 _ ?x ?y =>
                          apply Forall2_impl_In with (2:=H) end;
          intros; rewrite Henv in *; auto.
    - inv WTeq; rewrite <-Henv in *; eauto with nltyping;
        econstructor; eauto;
          match goal with H:Forall2 _ ?x ?y |- Forall2 _ ?x ?y =>
                          apply Forall2_impl_In with (2:=H) end;
          intros; rewrite Henv in *; auto.
  Qed.

End NLTYPING.

Module NLTypingFun
       (Ids     : IDS)
       (Op      : OPERATORS)
       (Clks    : CLOCKS   Ids)
       (ExprSyn : NLEXPRSYNTAX Op)
       (Syn     : NLSYNTAX Ids Op Clks ExprSyn)
       <: NLTYPING Ids Op Clks ExprSyn Syn.
  Include NLTYPING Ids Op Clks ExprSyn Syn.
End NLTypingFun.
