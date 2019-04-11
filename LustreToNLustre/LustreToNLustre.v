Require Import Velus.Common.
Require Import Velus.Operators.
Require Import Velus.Clocks.
Require Import Velus.Lustre.
Require Import Velus.CoreExpr.CESyntax.
Require Import Velus.NLustre.NLSyntax.

Require Import List.
Import List.ListNotations.
Import Permutation.

Open Scope list.

Require Import common.Errors.
Open Scope error_monad_scope.

Require Import Coq.Classes.EquivDec.

(** * Turn a normalized Lustre program into an NLustre program *)

Module Type LUSTRE_TO_NLUSTRE
       (Import Ids  : IDS)
       (Import Op   : OPERATORS)
       (L           : LSYNTAX  Ids Op)
       (CE          : CESYNTAX     Op)
       (NL          : NLSYNTAX Ids Op CE).

  Fixpoint to_lexp (e : L.exp) : res CE.lexp :=
    match e with
    | L.Econst c                 => OK (CE.Econst c)
    | L.Evar x (ty, ck)          => OK (CE.Evar x ty)
    | L.Eunop op e (ty, ck)      => do le <- to_lexp e;
                                    OK (CE.Eunop op le ty)
    | L.Ebinop op e1 e2 (ty, ck) => do le1 <- to_lexp e1;
                                    do le2 <- to_lexp e2;
                                    OK (CE.Ebinop op le1 le2 ty)
    | L.Ewhen [e] x b ([ty], ck) => do le <- to_lexp e;
                                    OK (CE.Ewhen le x b)
    | L.Efby _ _ _
    | L.Ewhen _ _ _ _
    | L.Emerge _ _ _ _
    | L.Eite _ _ _ _
    | L.Eapp _ _ _     => Error (msg "expression not normalized")
    end.

  (*
  Definition to_lexp' (les : option (list NL.lexp)) (e : L.exp) : option (list NL.lexp) :=
    match les, to_lexp e with
    | Some les', Some le => Some (le :: les')
    | _, _ => None
    end.

  Fixpoint to_lexps (es : list L.exp) : option (list NL.lexp) :=
    fold_left to_lexp' es (Some []).
   *)

  Fixpoint to_cexp (e : L.exp) : res CE.cexp :=
    match e with
    | L.Econst _
    | L.Evar _ _
    | L.Eunop _ _ _
    | L.Ebinop _ _ _ _
    | L.Ewhen _ _ _ _                 => do le <- to_lexp e;
                                         OK (CE.Eexp le)

    | L.Emerge x [et] [ef] ([ty], ck) => do cet <- to_cexp et;
                                         do cef <- to_cexp ef;
                                         OK (CE.Emerge x cet cef)

    | L.Eite e [et] [ef] ([ty], ck)   => do le <- to_lexp e;
                                         do cet <- to_cexp et;
                                         do cef <- to_cexp ef;
                                         OK (CE.Eite le cet cef)

    | L.Emerge _ _ _ _
    | L.Eite _ _ _ _
    | L.Efby _ _ _
    | L.Eapp _ _ _     => Error (msg "control expression not normalized")
    end.

  Fixpoint suffix_of_clock (ck : clock) (acc : list (ident * bool))
                                                    : list (ident * bool) :=
    match ck with
    | Cbase => acc
    | Con ck' x b => suffix_of_clock ck' ((x, b) :: acc)
    end.

  Fixpoint clock_of_suffix (sfx : list (ident * bool)) (ck : clock) : clock :=
    match sfx with
    | [] => ck
    | (x, b) :: sfx' => clock_of_suffix sfx' (Con ck x b)
    end.

  (* TODO: move to common *)
  Lemma app_tail_eq:
    forall {A} (xs ys zs : list A),
      xs = zs ->
      xs ++ ys = zs ++ ys.
  Proof.
    intros ** Heq. induction ys.
    now setoid_rewrite app_nil_r.
    now subst xs.
  Qed.

  Lemma suffix_of_clock_app:
    forall sfx sfx' ck,
      suffix_of_clock ck (sfx ++ sfx') = (suffix_of_clock ck sfx) ++ sfx'.
  Proof.
    intros sfx sfx'; revert sfx' sfx.
    induction sfx' as [|xb sfx' IH].
    now setoid_rewrite app_nil_r.
    intros sfx ck.
    rewrite <-app_last_app, IH, <-app_last_app  with (xs':=sfx').
    apply app_tail_eq.
    revert sfx; clear.
    induction ck; auto.
    simpl; intros sfx.
    now rewrite app_comm_cons, IHck.
  Qed.

  Lemma clock_of_suffix_app:
    forall sfx sfx' ck,
      clock_of_suffix (sfx ++ sfx') ck
      = clock_of_suffix sfx' (clock_of_suffix sfx ck).
  Proof.
    induction sfx as [|(x, b) sfx IH].
    now setoid_rewrite app_nil_l.
    intros sfx' ck.
    now simpl; rewrite IH.
  Qed.

  Remark clock_of_suffix_of_clock:
    forall ck,
      clock_of_suffix (suffix_of_clock ck []) Cbase = ck.
  Proof.
    induction ck; auto; simpl in *.
    now rewrite <-(app_nil_l [(i, b)]),
                suffix_of_clock_app, clock_of_suffix_app, IHck.
  Qed.

  Fixpoint common_suffix (sfx1 sfx2 : list (ident * bool))
                                                 : list (ident * bool) :=
    match sfx1, sfx2 with
    | [],  _ => []
    | _ , [] => []
    | (x1, b1)::sfx1', (x2, b2)::sfx2' =>
      if Pos.eqb x1 x2 && b1 ==b b2 then (x1, b1) :: common_suffix sfx1' sfx2'
      else []
    end.

  (* TODO: Maybe it would just be better to store the base clock of an
           application with the application... *)
  Definition find_base_clock (cks : list clock) : clock :=
    match cks with
    | [] => Cbase
    | ck::cks =>
      let sfx := fold_left
                   (fun sfx1 ck2 => common_suffix sfx1 (suffix_of_clock ck2 []))
                   cks (suffix_of_clock ck [])
      in
      clock_of_suffix sfx Cbase
    end.

  Definition find_clock (env : Env.t (type * clock)) (x : ident) : res clock :=
    match Env.find x env with
    | None => Error (msg "find_clock failed unexpectedly")
    | Some (ty, ck) => OK ck
    end.

  Fixpoint to_constant (e : L.exp) : res const :=
    match e with
    | L.Econst c => OK c
    | L.Ewhen [e] _ _ _ => to_constant e
    | _ => Error (msg "not a constant")
    end.

  Fixpoint clock_of_sclock (sck : sclock) : option clock :=
    match sck with
    | Sbase => Some Cbase
    | Son sck' (Vnm x) b =>
      option_map (fun ck' => Con ck' x b) (clock_of_sclock sck')
    | Son _ (Vidx _) _ =>
      None
    end.

  Definition get_exp_clock (acc : list clock) (sck : sclock) : list clock :=
    match clock_of_sclock sck with
    | None => acc
    | Some ck => ck :: acc
    end.

  Definition to_equation (env : Env.t (type * clock)) (eq : L.equation)
                                                          : res NL.equation :=
    match eq with
    | (xs, [L.Eapp f es _]) =>
        do xcks1 <- mmap (find_clock env) xs;
        do xcks2 <- OK (fold_left get_exp_clock (concat (map L.clockof es)) []);
        do les <- mmap to_lexp es;
        OK (NL.EqApp xs (find_base_clock (xcks1 ++ xcks2)) f les None)

    | ([x], [L.Efby [e0] [e] _]) =>
        do c0 <- to_constant e0;
        do ck <- find_clock env x;
        do le <- to_lexp e;
        OK (NL.EqFby x ck c0 le)

    | ([x], [e]) =>
        do ck <- find_clock env x;
        do ce <- to_cexp e;
        OK (NL.EqDef x ck ce)

    | _ => Error (msg "equation not normalized")
    end.

  Program Definition to_node (n : L.node) : res NL.node :=
    let env := Env.adds' n.(L.n_out)
                             (Env.adds' n.(L.n_vars)
                                            (Env.from_list n.(L.n_in)))
    in
    do neqs  <- mmap (to_equation env) n.(L.n_eqs);
    OK {|
        NL.n_name     := n.(L.n_name);
        NL.n_in       := n.(L.n_in);
        NL.n_out      := n.(L.n_out);
        NL.n_vars     := n.(L.n_vars);
        NL.n_eqs      := neqs;

        NL.n_ingt0    := _;
        NL.n_outgt0   := _;
        NL.n_defd     := _;
        NL.n_nodup    := _;
        NL.n_good     := _
      |}.
  Next Obligation.
    exact (L.n_ingt0 n).
  Qed.
  Next Obligation.
    exact (L.n_outgt0 n).
  Qed.
  Next Obligation.
    admit (* L.vars_defined = NL.vars_defined *).
  Qed.
  Next Obligation.
    admit.
  Qed.
  Next Obligation.
    exact (L.n_nodup n).
  Qed.
  Next Obligation.
    admit.
  Qed.

  Definition to_global (g : L.global) : res NL.global :=
    mmap to_node g.

  (* TODO: Show semantic preservation. *)

End LUSTRE_TO_NLUSTRE.

Module LustreToNLustreFun
       (Ids   : IDS)
       (Op    : OPERATORS)
       (LSyn  : LSYNTAX  Ids Op)
       (CESyn : CESYNTAX     Op)
       (NLSyn : NLSYNTAX Ids Op CESyn)
       <: LUSTRE_TO_NLUSTRE Ids Op LSyn CESyn NLSyn.
  Include LUSTRE_TO_NLUSTRE Ids Op LSyn CESyn NLSyn.
End LustreToNLustreFun.
