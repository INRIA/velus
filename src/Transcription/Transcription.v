From Velus Require Import Common.
From Velus Require Import Environment.
From Velus Require Import Operators.
From Velus Require Import Clocks.
From Velus Require Import Lustre.LSyntax.
From Velus Require Import CoreExpr.CESyntax.
From Velus Require Import NLustre.NLSyntax.

From Coq Require Import String.

From Coq Require Import List.
Import List.ListNotations.

From compcert Require Import common.Errors.
Open Scope error_monad_scope.

(** * Turn a normalized Lustre program into an NLustre program *)

Module Type TRANSCRIPTION
       (Import Ids  : IDS)
       (Import Op   : OPERATORS)
       (Import OpAux: OPERATORS_AUX Op)
       (L           : LSYNTAX  Ids Op)
       (Import CE   : CESYNTAX     Op)
       (NL          : NLSYNTAX Ids Op CE).

  Fixpoint to_lexp (e : L.exp) : res CE.exp :=
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
    | L.Eapp _ _ _ _    => Error (msg "expression not normalized")
    end.

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
    | L.Eapp _ _ _ _    => Error (msg "control expression not normalized")
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

  Lemma suffix_of_clock_app:
    forall sfx sfx' ck,
      suffix_of_clock ck (sfx ++ sfx') = (suffix_of_clock ck sfx) ++ sfx'.
  Proof.
    intros sfx sfx'; revert sfx' sfx.
    induction sfx' as [|xb sfx' IH].
    now setoid_rewrite app_nil_r.
    intros sfx ck.
    rewrite <-app_last_app, IH, <-app_last_app  with (xs':=sfx'). f_equal.
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
      if (Pos.eqb x1 x2) && (b1 ==b b2) then (x1, b1) :: common_suffix sfx1' sfx2'
      else []
    end.

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

  Definition to_equation (env : Env.t (type * clock)) (envo : ident -> res unit)
                         (eq : L.equation) : res NL.equation :=
    match eq with
    | (xs, [L.Eapp f es None _]) =>
        do les <- mmap to_lexp es;
        OK (NL.EqApp xs (find_base_clock (L.clocksof es)) f les None)

    | ([x], [L.Efby [e0] [e] _]) =>
        do _  <- envo x;
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

  Lemma find_clock_in :
    forall x env ty ck,
      Env.find x env = Some (ty, ck) ->
      find_clock env x = OK ck.
  Proof.
    intros * H. unfold find_clock. now rewrite H.
  Qed.

  Lemma ok_fst_defined eq eq' :
    forall env envo,
      to_equation env envo eq = OK eq' -> fst eq = NL.var_defined eq'.
  Proof.
    intros env envo Htoeq.
    unfold to_equation in Htoeq.
    cases; monadInv Htoeq; inv EQ; simpl; auto.
  Qed.

  Lemma nl_vars_defined_cons:
    forall eq eqs,
      NL.vars_defined (eq::eqs) = NL.var_defined eq ++ NL.vars_defined eqs.
  Proof.
    intros. unfold NL.vars_defined. now simpl.
  Qed.

  Remark mmap_cons:
    forall (A B: Type) (f: A -> res B) (l: list A) (r: list B) (x: A),
      mmap f (x :: l) = OK r ->
      exists x' l', r = x' :: l' /\ f x = OK x' /\ mmap f l = OK l'.
  Proof.
    induction l; simpl; intros.
    monadInv H. exists x0, []. auto.
    monadInv H. exists x0, x1. auto.
  Qed.

  Remark mmap_cons2:
    forall (A B: Type) (f: A -> res B) (l: list A) (r: list B) (x: B),
      mmap f (l) = OK (x :: r) ->
      exists x' l', l = x' :: l' /\ f x' = OK x /\ mmap f l' = OK r.
  Proof.
    induction l; simpl; intros.
    monadInv H.
    monadInv H. exists a, l. auto.
  Qed.

  Remark mmap_cons3:
    forall (A B: Type) (f: A -> res B) (l: list A) (r: list B) (x: A) (y : B),
      mmap f (x :: l) = OK (y :: r) ->
      f x = OK y /\ mmap f l = OK r.
  Proof.
    induction l; simpl; intros; monadInv H; auto.
  Qed.

  Definition mmap_to_equation env envo n :
    res { neqs | mmap (to_equation env envo) n.(L.n_eqs) = OK neqs }.
  Proof.
    destruct (mmap (to_equation env envo) n.(L.n_eqs)).
    left. eauto.
    right. auto.
  Defined.

  Unset Program Cases.
  Program Definition to_node (n : L.node) : res NL.node :=
    let envo := Env.from_list n.(L.n_out) in
    let env := Env.adds' n.(L.n_vars) (Env.adds' n.(L.n_in) envo) in
    let is_not_out :=
        fun x => if Env.mem x envo
              then Error (msg "output variable defined as a fby")
              else OK tt in
    match mmap_to_equation env is_not_out n (* return _ *) with
    | OK (exist neqs P) =>
      OK {|
          NL.n_name     := n.(L.n_name);
          NL.n_in       := n.(L.n_in);
          NL.n_out      := n.(L.n_out);
          NL.n_vars     := n.(L.n_vars);
          NL.n_eqs      := neqs;

          NL.n_ingt0    := L.n_ingt0 n;
          NL.n_outgt0   := L.n_outgt0 n;
          NL.n_defd     := _;
          NL.n_vout     := _;
          NL.n_nodup    := L.n_nodup n;
          NL.n_good     := _
        |}
    | Error e => Error e
    end.

  (* NL.n_defd obligation *)
  Next Obligation.
    clear H0 H.
    monadInv P.
    assert (NL.vars_defined neqs = L.vars_defined (L.n_eqs n)). clear P.
    { revert H. revert neqs. induction (L.n_eqs n); simpl.
    - intros neqs Htr. inv Htr. auto.
    - intros neqs Htoeq. inv Htoeq.
      apply IHl in H3. simpl.
      apply ok_fst_defined in H1. rewrite H3. now rewrite <- H1.
    }
    rewrite H0.
    exact (L.n_defd n).
  Qed.

  (* NL.n_vout obligation *)
  Next Obligation.
    clear H H1. rename H0 into Hin. rename P into Heqr.

    monadInv Heqr. induction H as [| eq leq eq' leq' Htoeq ].
    intro Hbad. inv Hbad.
    assert (Hmmap := Heqr).
    apply mmap_cons2 in Heqr.
    destruct Heqr as (eq'' & leq'' & Heqs' & Htoeq' & Hmmap').
    inv Heqs'.
    simpl. destruct (NL.is_fby eq') eqn:?.
    - unfold NL.vars_defined, flat_map. simpl. rewrite in_app.
      intro Hi. destruct Hi.
      + unfold to_equation in Htoeq. destruct eq''.
        cases_eqn E; monadInv1 Htoeq; inv Heqb.
        simpl in H0. destruct H0; auto. subst. inv EQ.
        apply Env.Props.P.F.not_mem_in_iff in E8. apply E8.
        rewrite in_map_iff in Hin.
        destruct Hin as ((x & ?) & Hfst & Hin). inv Hfst.
        eapply Env.find_In. eapply Env.In_find_adds'; simpl; eauto.
        destruct n. simpl. assert (Hnodup := n_nodup).
        now repeat apply NoDupMembers_app_r in Hnodup.
      + apply IHlist_forall2; auto.
    - apply IHlist_forall2; eauto.
  Qed.

  (* NL.n_good obligation *)
  Next Obligation.
    exact (L.n_good n).
  Qed.

  Definition to_global (g : L.global) : res NL.global :=
    mmap to_node g.


  Ltac tonodeInv H :=
    match type of H with
    | (to_node ?n = OK _) =>
      let Hs := fresh in
      let Hmmap := fresh "Hmmap" in
      unfold to_node in H;
      destruct(mmap_to_equation
               (Env.adds' (L.n_vars n)
                (Env.adds' (L.n_in n)
                 (Env.from_list (L.n_out n))))
            (fun x : Env.key =>
             if Env.mem x (Env.from_list (L.n_out n))
             then Error (msg "output variable defined as a fby")
             else OK tt) n)
      as [ Hs | Hs ];
      try (destruct Hs as (? & Hmmap)); inv H
    end.

  Lemma find_node_hd f a G n :
    L.find_node f (a :: G) = Some n ->
    ((ident_eqb (L.n_name a) f) = true  /\ a = n) \/
    ((ident_eqb (L.n_name a) f) = false /\ L.find_node f G = Some n).
  Proof.
    simpl. intro.
    case_eq (ident_eqb (L.n_name a) f); intro; rewrite H0 in H; inv H.
    auto. right. auto.
  Qed.

  Lemma find_node_In :
    forall f G n, L.find_node f G = Some n -> In n G.
  Proof.
    induction G; intros * Hfind; try discriminate.
    inv Hfind. destruct (ident_eqb (L.n_name a) f).
    inv H0. simpl. now left.
    simpl. right. now apply IHG.
  Qed.

  Lemma to_node_name n n' :
    to_node n = OK n' -> L.n_name n = NL.n_name n'.
  Proof.
    intro Htr. tonodeInv Htr. now simpl.
  Qed.

  Lemma to_node_in n n' :
    to_node n = OK n' -> L.n_in n = NL.n_in n'.
  Proof.
    intro Htr. tonodeInv Htr. now simpl.
  Qed.

  Lemma to_node_out n n' :
    to_node n = OK n' -> L.n_out n = NL.n_out n'.
  Proof.
    intro Htr. tonodeInv Htr. now simpl.
  Qed.

  Lemma to_node_vars n n' :
    to_node n = OK n' -> L.n_vars n = NL.n_vars n'.
  Proof.
    intro Htr. tonodeInv Htr. now simpl.
  Qed.

  Lemma find_node_global (G: L.global) (P: NL.global) (f: ident) (n: L.node) :
    to_global G = OK P ->
    L.find_node f G = Some n ->
    exists n', NL.find_node f P = Some n' /\ to_node n = OK n'.
  Proof.
    revert P.
    induction G; intros P Htrans Hfind. inversion Hfind.
    apply find_node_hd in Hfind.
    destruct Hfind.
    - inv H. apply mmap_cons in Htrans.
      destruct Htrans as [ n' [ l' [ Hp [ Hnode Hmmap ]]]]; subst.
      exists n'.
      remember Hnode as Heq; clear HeqHeq. apply to_node_name in Heq.
      split; auto. simpl. rewrite <- Heq. rewrite H0. reflexivity.
    - destruct H as [ Hneq Hfind ].
      apply mmap_cons in Htrans.
      destruct Htrans as [ n' [P' [nP [Hton  Htrans]]]]. subst.
      apply IHG in Htrans; auto. destruct Htrans. destruct H as [ H Hnode ].
      exists x. split; auto. apply NL.find_node_other; auto.
      apply to_node_name in Hton. rewrite <- Hton. apply ident_eqb_neq. auto.
  Qed.

End TRANSCRIPTION.

Module TranscriptionFun
       (Ids   : IDS)
       (Op    : OPERATORS)
       (OpAux : OPERATORS_AUX Op)
       (L     : LSYNTAX  Ids Op)
       (CE    : CESYNTAX     Op)
       (NL    : NLSYNTAX Ids Op CE)
       <: TRANSCRIPTION Ids Op OpAux L CE NL.
  Include TRANSCRIPTION Ids Op OpAux L CE NL.
End TranscriptionFun.
