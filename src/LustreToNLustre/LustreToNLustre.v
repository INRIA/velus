From Velus Require Import Common.
From Velus Require Import Environment.
From Velus Require Import Operators.
From Velus Require Import Clocks.
From Velus Require Import Lustre.
From Velus Require Import CoreExpr.CESyntax.
From Velus Require Import NLustre.NLSyntax.
From Velus Require Import NLustre.Streams.
From Velus Require Import NLustre.NLOrdered.
From Velus Require Import NLustre.NLSemanticsCoInd.

From Coq Require Import String.

From Coq Require Import List.
Import List.ListNotations.
From Coq Require Import Permutation.
From Coq Require Import Omega.

Open Scope list.

From compcert Require Import common.Errors.
Open Scope error_monad_scope.

From Coq Require Import Classes.EquivDec.

(** * Turn a normalized Lustre program into an NLustre program *)

Module Type LUSTRE_TO_NLUSTRE
       (Import Ids  : IDS)
       (Import Op   : OPERATORS)
       (Import OpAux: OPERATORS_AUX Op)
       (L           : LSYNTAX  Ids Op)
       (Import CE   : CESYNTAX     Op)
       (NL          : NLSYNTAX Ids Op CE)
       (LT          : LTYPING  Ids Op L)
       (LC          : LCLOCKING Ids Op L)
       (Ord         : NLORDERED Ids Op CE     NL)
       (Lord        : LORDERED   Ids Op       L)
       (LS          : LSEMANTICS Ids Op OpAux L Lord)
       (NLSC        : NLSEMANTICSCOIND Ids Op OpAux CE NL Ord).

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

  Definition to_equation (env : Env.t (type * clock)) (envo : ident -> res unit)
                         (eq : L.equation) : res NL.equation :=
    match eq with
    | (xs, [L.Eapp f es _]) =>
        do xcks1 <- mmap (find_clock env) xs;
        do xcks2 <- OK (L.clocksof es);
        do les <- mmap to_lexp es;
        OK (NL.EqApp xs (find_base_clock (xcks1 ++ xcks2)) f les None)

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
  Admitted.

  Definition to_global (g : L.global) : res NL.global :=
    mmap to_node g.



  (* Proofs for semantics *)

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
    to_node n = OK n' -> (LS.idents (L.n_in n)) = (NLSC.idents (NL.n_in n')).
  Proof.
    intro Htr. tonodeInv Htr. now simpl.
  Qed.

  Lemma to_node_out n n' :
    to_node n = OK n' -> (LS.idents (L.n_out n)) = (NLSC.idents (NL.n_out n')).
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

  Lemma const_eq :
    forall c b, NLSC.const c b ≡ LS.const c b.
  Proof.
    cofix Cofix. intros.
    unfold_Stv b; constructor; simpl; auto.
  Qed.

  Lemma const_inv1 :
    forall c b s,
      LS.const c b ≡ absent ::: s ->
      exists b', s ≡ LS.const c b' /\ b ≡ false ::: b'.
  Proof.
    intros * H.
    unfold_Stv b; inv H; simpl in *; inv H0.
    exists b. split; symmetry; auto. reflexivity.
  Qed.

  Lemma const_inv2 :
    forall c c' b s,
      LS.const c b ≡ present c' ::: s ->
      exists b', s ≡ LS.const c b'
            /\ b ≡ true ::: b'
            /\ c' = sem_const c.
  Proof.
    intros * H.
    unfold_Stv b; inv H; simpl in *; inv H0.
    exists b. split. symmetry. assumption. split; reflexivity.
  Qed.

  Lemma const_tl :
    forall c b v tl,
      LS.const c b ≡ v ::: tl ->
      LS.const c (Streams.tl b) ≡ tl.
  Proof.
    intros * H.
    unfold_Stv b; inv H; simpl in *; inv H0; assumption.
  Qed.

  Lemma sem_var_var :
    forall H x s,
      LS.sem_var H x s <-> NLSC.sem_var H x s.
  Proof.
    split; intros * Hsem; inv Hsem;
    econstructor; eauto.
  Qed.

  Lemma env_maps_tl :
    forall i v s H,
      Env.MapsTo i (v ::: s) H -> Env.MapsTo i s (NLSC.History_tl H).
  Proof.
    intros * Hmap.
    unfold NLSC.History_tl.
    assert (s = Streams.tl (v ::: s)) as Hs by auto.
    rewrite Hs. eapply Env.map_1. assumption.
  Qed.

  Lemma sem_var_step :
    forall H x v s,
      LS.sem_var H x (v ::: s) -> LS.sem_var (NLSC.History_tl H) x s.
  Proof.
    intros * Hsem.
    inv Hsem.
    destruct xs'.
    econstructor.
    eapply env_maps_tl; eauto. now inv H2.
  Qed.

  Lemma sem_var_step_nl :
    forall H x v s,
      NLSC.sem_var H x (v ::: s) -> NLSC.sem_var (NLSC.History_tl H) x s.
  Proof.
    intros * Hsem.
    inv Hsem.
    destruct xs'.
    econstructor.
    eapply env_maps_tl; eauto. now inv H2.
  Qed.

  Lemma sem_clock_step :
    forall H b ck s ss,
      NLSC.sem_clock H b ck (s ::: ss) ->
      NLSC.sem_clock (NLSC.History_tl H) (Streams.tl b) ck ss.
  Proof.
    intros * Hsem.
    inv Hsem; auto. econstructor. rewrite H1. simpl. reflexivity.
  Qed.

  Lemma sem_const_step :
    forall G H b e e' v s,
      to_constant e = OK e' ->
      LS.sem_exp G H b e [v ::: s] ->
      LS.sem_exp G (NLSC.History_tl H) (Streams.tl b) e [s].
  Proof.
    einduction e using L.exp_ind2; intros * Htr Hsem; inv Htr.
    - inv Hsem. symmetry in H5.
      destruct v;
        [ apply const_inv1 in H5; destruct H5 as [ b' [ Hs Hb ] ]
        | apply const_inv2 in H5; destruct H5 as (b' & Hs & Hb & Hc) ];
        rewrite Hs; rewrite Hb; simpl; econstructor; reflexivity.
    - destruct es; inv H2.
      destruct es; inv H3.
      inv H0. inv H5. inv Hsem. inv H12. inv H10. inv H9. inv H6. inv H0.
      rewrite app_nil_r in H3. inv H3.
      destruct x0. destruct s0.
      econstructor. econstructor; eauto.
      eapply sem_var_step; eauto. econstructor; eauto.
      now inv H5.
  Qed.

    Lemma sem_lexp_step :
    forall G H b e e' v s,
      to_lexp e = OK e' ->
      LS.sem_exp G H b e [v ::: s] ->
      LS.sem_exp G (NLSC.History_tl H) (Streams.tl b) e [s].
  Proof.
    einduction e using L.exp_ind2; intros * Htr Hsem; inv Htr.
    - inv Hsem. symmetry in H5.
      destruct v;
        [ apply const_inv1 in H5; destruct H5 as [ b' [ Hs Hb ] ]
        | apply const_inv2 in H5; destruct H5 as (b' & Hs & Hb & Hc) ];
      rewrite Hs; rewrite Hb; simpl; econstructor; reflexivity.
    - inv Hsem. inv H5.  destruct xs'.
      econstructor. econstructor.
      eapply env_maps_tl; eauto. inv H3; simpl in *. assumption.
    - inv Hsem. destruct a. monadInv H1. destruct s0.
      econstructor; eauto. inv H10; auto.
    - inv Hsem. destruct a. monadInv H1. destruct s1, s2.
      econstructor; eauto. inv H13; auto.
    - destruct es; inv H2.
      destruct es; inv H3.
      inv H0.
      destruct a. destruct l; inv H2.
      destruct l; try now inv H1. monadInv H1.
      clear H5.
      inv Hsem. inv H11. inv H5. destruct s0, x1.
      inv H9. inv H7. simpl in H0. rewrite app_nil_r in H0. subst.
      econstructor.
      + econstructor; eauto.
      + eapply sem_var_step. eassumption.
      + econstructor; eauto. inv H3; eauto.
  Qed.

  Lemma sem_cexp_step :
    forall G H b e e' v s,
      to_cexp e = OK e' ->
      LS.sem_exp G H b e [v ::: s] ->
      LS.sem_exp G (NLSC.History_tl H) (Streams.tl b) e [s].
  Proof.
    einduction e using L.exp_ind2; intros * Htr Hsem;
      (now inv Htr) || (unfold to_cexp in Htr;
                       try (monadInv Htr; eapply sem_lexp_step; eauto));
      cases; monadInv Htr; fold to_cexp in *;

        inv Hsem; inv H11; inv H6; inv H12; inv H7; inv H13; inv H10;
          rewrite app_nil_r in H3, H2; subst;
            inv H0; inv H1; clear H10 H7; destruct x2, y1.
    - inv H8;
        (econstructor; eauto;
         [ eapply sem_var_step; eauto | econstructor; eauto; econstructor ]).
    - inv H8;
        (econstructor; eauto; eapply sem_lexp_step in EQ; eauto;
         econstructor; eauto; constructor).
  Qed.

  Lemma lift1_id :
    forall op ty xs rs, LS.lift1 op ty xs rs -> NLSC.lift1 op ty xs rs.
  Proof.
    cofix Cofix.
    intros * Hlift.
    unfold_Stv xs; unfold_Stv rs; inv Hlift;
      econstructor; eauto; eapply Cofix; eauto.
  Qed.

  Lemma lift2_id :
    forall op ty1 ty2 xs ys rs,
      LS.lift2 op ty1 ty2 xs ys rs -> NLSC.lift2 op ty1 ty2 xs ys rs.
  Proof.
    cofix Cofix.
    intros * Hlift.
    unfold_Stv xs; unfold_Stv rs; inv Hlift;
      econstructor; eauto; eapply Cofix; eauto.
  Qed.

  Lemma when_id :
    forall k xs cs rs, LS.when k cs xs rs -> NLSC.when k xs cs rs.
  Proof.
    cofix Cofix.
    intros * Hwhen.
    unfold_Stv xs; unfold_Stv cs; inv Hwhen;
      econstructor; eauto; eapply Cofix; eauto.
  Qed.

  Lemma merge_id :
    forall k xs cs rs, LS.merge k xs cs rs -> NLSC.merge k xs cs rs.
  Proof.
    cofix Cofix.
    intros * Hwhen.
    unfold_Stv xs; unfold_Stv cs; inv Hwhen;
      econstructor; eauto; eapply Cofix; eauto.
  Qed.

  Lemma ite_id :
    forall k xs cs rs, LS.ite k xs cs rs -> NLSC.ite k xs cs rs.
  Proof.
    cofix Cofix.
    intros * Hwhen.
    unfold_Stv xs; unfold_Stv cs; inv Hwhen;
      econstructor; eauto; eapply Cofix; eauto.
  Qed.

  Lemma ty_lexp :
    forall G env e e',
      LT.wt_exp G env e ->
      to_lexp e = OK e' ->
      L.typeof e = [CE.typeof e'].
  Proof.
    induction e using L.exp_ind2; intros * Hwt Htr; inv Htr.
    - now simpl.
    - destruct a. inv H0. now simpl.
    - destruct a. simpl. monadInv H0. now simpl.
    - destruct a. monadInv H0. now simpl.
    - cases. inv H. simpl. inv Hwt. inv H8. inv H6. monadInv H1.
      unfold L.typesof. unfold flat_map. simpl. rewrite app_nil_r.
      now apply H3.
  Qed.

  Lemma sem_exp_lexp :
    forall G G' env H b e e' s,
      LT.wt_exp G' env e ->
      to_lexp e = OK e' ->
      LS.sem_exp G H b e [s] ->
      NLSC.sem_lexp H b e' s.
  Proof.
    induction e using L.exp_ind2; intros * Hwt Htr Hsem; inv Htr.
    - inv Hsem. econstructor. now rewrite const_eq.
    - destruct a. inv Hsem. inv H1. econstructor. now apply sem_var_var.
    - destruct a. inv Hsem. monadInv H1. inv Hwt. econstructor; eauto.
      apply lift1_id. eapply ty_lexp in EQ; eauto. rewrite H9 in EQ. now inv EQ.
    - destruct a. inv Hsem. monadInv H1. inv Hwt. econstructor; eauto.
      apply lift2_id. eapply ty_lexp in EQ; eauto. eapply ty_lexp in EQ1; eauto.
      rewrite H11 in EQ. inv EQ. rewrite H12 in EQ1. now inv EQ1.
    - cases. monadInv H2. inv Hsem. inv H0. clear H4. inv Hwt.
      inv H9. inv H5. inv H11. inv H6. rewrite app_nil_r in H0. inv H0. inv H14.
      econstructor. eapply H3; eauto. eapply sem_var_var. eassumption.
      now eapply when_id.
  Qed.

  Lemma sem_lexp_single :
    forall e e' G H b ss,
      to_lexp e = OK e' ->
      LS.sem_exp G H b e ss ->
      exists s, ss = [s].
  Proof.
    induction e using L.exp_ind2; intros * Htr Hsem; inv Htr;
      try (inv Hsem; eexists; now eauto).
    cases_eqn H2. subst. monadInv H2. inv Hsem. inv H9. inv H5. inv H. inv H5.
    eapply H4 in EQ; [|eauto]. inv EQ. simpl in H11. inv H11. inv H6.
    eauto.
  Qed.

  Lemma sem_exps_lexps :
    forall G H b tenv es les ss,
      mmap to_lexp es = OK les ->
      Forall (LT.wt_exp G tenv) es ->
      Forall2 (LS.sem_exp G H b) es ss ->
      Forall2 (NLSC.sem_lexp H b) les (concat ss).
  Proof.
    intros * Hmmap Hwt Hsem. revert dependent les.
    induction Hsem; intros. inv Hmmap. simpl. auto.
    apply mmap_cons in Hmmap.
    destruct Hmmap as [ x' [le' [Hle [Htolexp  Hmmap]]]]. inv Hwt.
    apply IHHsem in Hmmap; eauto.
    assert (Htolexp' := Htolexp).
    eapply sem_lexp_single in Htolexp'; eauto. inv Htolexp'.
    eapply sem_exp_lexp in Htolexp; eauto. now constructor.
  Qed.

  Lemma sem_exp_cexp :
    forall G G' env H b e e' s,
      LT.wt_exp G' env e ->
      to_cexp e = OK e' ->
      LS.sem_exp G H b e [s] ->
      NLSC.sem_cexp H b e' s.
  Proof.
    induction e using L.exp_ind2; intros * Hwt Htr Hsem;
      (now inv Htr) || (unfold to_cexp in Htr;
                       try (monadInv Htr; econstructor;
                            eapply sem_exp_lexp; eauto));
      cases; monadInv Htr; fold to_cexp in *;
                 inv Hsem; inv H11; inv H6; inv H12; inv H7; inv H13; inv H10;
                   rewrite app_nil_r in H3, H2; subst;
                     inv H0; inv H1; clear H10 H7; destruct x2, y1.
    - inv Hwt; inv H11; inv H12. inv H8;
        (econstructor; eauto;
         [ eapply sem_var_var; eauto
         | econstructor; eauto; eapply merge_id; eauto ]).
    - inv Hwt. inv H12. inv H13.
      inv H8; econstructor; eauto;
        eapply sem_exp_lexp in EQ; eauto;
          econstructor; now apply ite_id.
  Qed.

  CoFixpoint abstract_clock (xs: Stream value) : Stream bool:=
    match xs with
    | absent ::: xs => false ::: abstract_clock xs
    | present _ ::: xs => true ::: abstract_clock xs
    end.

  Lemma length_typeof :
    forall G H b env e os,
      LT.wt_exp G env e ->
      LS.sem_exp G H b e os ->
      length (L.typeof e) = length os.
  Proof.
    induction e using L.exp_ind2; intros * Hwt Hsem;
      try (inv Hsem; inv Hwt; simpl; reflexivity).
    - inv Hsem. inv Hwt. simpl.
      rewrite <- H7. apply Forall3_length in H11. destruct H11.
      rewrite <- H3. unfold L.typesof, flat_map.
      clear H7 H9 H2 H3. revert dependent sss. induction es; intros.
      + inv H10. auto.
      + inv H10. inv H1. inv H6. simpl.
        rewrite app_length. rewrite app_length.
        f_equal. apply H7; auto.
        apply IHes; auto.
    - inv Hsem. inv Hwt. simpl.
      apply Forall2_length in H11. rewrite <- H11.
      clear H11. revert dependent ss. induction es; intros.
      + inv H9. auto.
      + inv H9. inv H0. inv H5. unfold L.typesof, flat_map. simpl.
        rewrite app_length. rewrite app_length.
        f_equal. apply H4; auto.
        apply IHes; auto.
    - inv Hsem. inv Hwt. simpl.
      apply Forall3_length in H13. destruct H13.
      rewrite <- H3, <- H2. unfold L.typesof, flat_map.
      clear H7 H9 H2 H3 H14. revert dependent ts. induction ets; intros.
      + inv H11. auto.
      + inv H11. inv H0. inv H6. simpl.
        rewrite app_length. rewrite app_length.
        f_equal. apply H5; auto.
        apply IHets; auto.
    - inv Hsem. inv Hwt. simpl.
      apply Forall3_length in H13. destruct H13.
      rewrite <- H3, <- H2. unfold L.typesof, flat_map.
      clear H9 H2 H3 H15. revert dependent ts. induction ets; intros.
      + inv H11. auto.
      + inv H11. inv H0. inv H7. simpl.
        rewrite app_length. rewrite app_length.
        f_equal. apply H5; auto.
        apply IHets; auto.
    - inv Hsem. inv H9. inv Hwt. rewrite H2 in H12. inv H12.
      simpl. rewrite map_length.
      apply Forall2_length in H14. rewrite H14.
      apply Forall2_length in H4. rewrite <- H4.
      clear - n0.
      induction (L.n_out n0); auto. simpl. f_equal. apply IHl.
  Qed.

  Lemma length_clockof :
    forall G H b env e os,
      LC.wc_exp G env e ->
      LS.sem_exp G H b e os ->
      length (L.clockof e) = length os.
  Proof.
    induction e using L.exp_ind2; intros * Hwc Hsem;
      try (inv Hsem; inv Hwc; simpl; reflexivity); inv Hsem.
    - inv Hwc. simpl.
      apply Forall2_length in H7. rewrite H7.
      apply Forall3_length in H11. destruct H11.
      rewrite <- H3, <- H2. unfold L.clocksof, flat_map.
      clear H2 H3 H7.
      revert dependent s0ss. induction e0s; intros.
      + inv H8. auto.
      + inv H8. inv H0. simpl.
        rewrite app_length. rewrite app_length. inv H5.
        f_equal. apply H7; auto.
        apply IHe0s; auto.
    - inv Hwc. simpl. rewrite map_length. rewrite H8.
      apply Forall2_length in H11. rewrite <- H11.
      clear H11 H7 H8. revert dependent ss. induction es; intros.
      + inv H9. auto.
      + inv H9. inv H0. inv H5. unfold L.clocksof, flat_map. simpl.
        rewrite app_length. rewrite app_length.
        f_equal. apply H4; auto.
        apply IHes; auto.
    - inv Hwc. simpl. rewrite map_length. rewrite H15.
      apply Forall3_length in H13. destruct H13.
      rewrite <- H3, <- H2. unfold L.clocksof, flat_map.
      clear H7 H9 H2 H3 H14 H10 H15 H16. revert dependent ts.
      induction ets; intros.
      + inv H11. auto.
      + inv H11. inv H0. inv H6. simpl.
        rewrite app_length. rewrite app_length.
        f_equal. apply H5; auto.
        apply IHets; auto.
    - inv Hwc. simpl. rewrite map_length. rewrite H16.
      apply Forall3_length in H13. destruct H13.
      rewrite <- H3, <- H2. unfold L.clocksof, flat_map.
      clear H9 H2 H3 H15 H14 H16 H17. revert dependent ts.
      induction ets; intros.
      + inv H11. auto.
      + inv H11. inv H0. inv H7. simpl.
        rewrite app_length. rewrite app_length.
        f_equal. apply H5; auto.
        apply IHets; auto.
    - inv H9. inv Hwc. rewrite H2 in H12. inv H12.
      apply Forall2_length in H4. rewrite <- H4.
      destruct H13 as (?&?&?&Hnout).
      apply Forall2_length in Hnout. rewrite map_length in Hnout.
      simpl. rewrite map_length. rewrite <- Hnout.
      clear - n0.
      induction (L.n_out n0); auto. simpl. f_equal. apply IHl.
  Qed.

  Lemma ac_when :
    forall k cs xs rs,
      LS.when k cs xs rs -> abstract_clock cs ≡ abstract_clock xs.
  Proof.
    cofix Cofix.
    intros * Hwhen. inv Hwhen; econstructor; simpl; eauto.
  Qed.

  Lemma ac_const:
    forall c b cs,
      LS.const c b ≡ cs -> b ≡ abstract_clock cs.
  Proof.
    cofix Cofix.
    intros * Hconst.
    unfold_Stv b;
      inv Hconst; simpl in *;
      unfold_Stv cs; constructor; simpl; eauto; inv H.
  Qed.

  Lemma ac_fby1 :
    forall xs ys rs,
      LS.fby xs ys rs -> abstract_clock xs ≡ abstract_clock rs.
  Proof.
    cofix Cofix.
    intros * Hfby.
    unfold_Stv xs; inv Hfby; econstructor; simpl; eauto.
    clear - H3. revert H3. revert y xs ys0 rs0.
    cofix Cofix.
    intros * Hfby1.
    unfold_Stv xs; inv Hfby1; econstructor; simpl; eauto.
  Qed.

  Lemma ac_fby2 :
    forall xs ys rs,
      LS.fby xs ys rs -> abstract_clock ys ≡ abstract_clock rs.
  Proof.
    cofix Cofix. intros * Hfby.
    unfold_Stv ys; inv Hfby; econstructor; simpl; eauto.
    clear - H3. revert H3. revert c ys xs0 rs0.
    cofix Cofix. intros * Hfby1.
    unfold_Stv ys; inv Hfby1; econstructor; simpl; eauto.
  Qed.

  Lemma ac_ite :
    forall s  ts fs rs,
      LS.ite s ts fs rs -> abstract_clock ts ≡ abstract_clock rs.
  Proof.
    cofix Cofix.
    intros * Hite.
    unfold_Stv ts; inv Hite; econstructor; simpl; eauto.
  Qed.

  Lemma ac_lift1 :
    forall op ty s o,
      LS.lift1 op ty s o -> abstract_clock s ≡ abstract_clock o.
  Proof.
    cofix Cofix.
    intros * Hlift.
    unfold_Stv s; inv Hlift; econstructor; simpl; eauto.
  Qed.

  Lemma ac_lift2 :
    forall op ty1 ty2 s1 s2 o,
      LS.lift2 op ty1 ty2 s1 s2 o -> abstract_clock s1 ≡ abstract_clock o.
  Proof.
    cofix Cofix.
    intros * Hlift.
    unfold_Stv s1; inv Hlift; econstructor; simpl; eauto.
  Qed.

  Inductive Is_free_left (x : ident) : L.exp -> Prop :=
  | IFLvar : forall a,
      Is_free_left x (L.Evar x a)
  | IFLunop : forall op e a,
      Is_free_left x e ->
      Is_free_left x (L.Eunop op e a)
  | IFLbinop : forall op e1 e2 a,
      Is_free_left x e1
      \/ Is_free_left x e2 ->
      Is_free_left x (L.Ebinop op e1 e2 a)
  | IFLfby : forall e0s es a,
      Exists (Is_free_left x) e0s ->
      Is_free_left x (L.Efby e0s es a)
  | IFLwhen : forall es y b a,
      x = y
      \/ Exists (Is_free_left x) es ->
      Is_free_left x (L.Ewhen es y b a)
  | IFLmerge : forall ets efs y a,
      x = y
      \/ Exists (Is_free_left x) ets
      \/ Exists (Is_free_left x) efs ->
      Is_free_left x (L.Emerge y ets efs a)
  | IFLite : forall e ets efs a,
      Is_free_left x e
      \/ Exists (Is_free_left x) ets
      \/ Exists (Is_free_left x) efs ->
      Is_free_left x (L.Eite e ets efs a)
  | IFLapp : forall f es a,
      Exists (Is_free_left x) es ->
      Is_free_left x (L.Eapp f es a).

  Lemma Forall2_const_map :
    forall (A B C : Type) (P : A -> B -> Prop) (e : A) (l : list C) (l' : list B),
      Forall (fun y => P e y) l' ->
      length l = length l' ->
      Forall2 (fun x y => P x y) (map (fun _ => e) l) l'.
  Proof.
    intros * Hf Hlen.
    apply Forall2_forall; split; [| now rewrite map_length].
    intros * Hin. revert dependent l'.
    induction l; intros. inv Hin.
    destruct l'; inv Hlen. simpl in Hin.
    destruct Hin; inv Hf; try inv H; eauto.
  Qed.

  Definition var_inv (D : positive -> Prop) (env : list (ident * clock)) : Prop :=
    forall x, D x ->
         (forall H b ck x xs,
             In (x, ck) env ->
             LS.sem_var H x xs ->
             NLSC.sem_clock H b ck (abstract_clock xs)).

  Lemma var_inv_weaken:
    forall (D1 D2 : positive -> Prop) (env : list (ident * clock)),
      var_inv D1 env ->
      (forall x, D2 x -> D1 x) ->
      var_inv D2 env.
  Proof.
    intros D1 D2 env I1 H12 x D2x.
    now apply H12, I1 in D2x.
  Qed.

  Definition envs_eq (env : Env.t (type * clock))
             (cenv : list (ident * clock)) :=
    forall (x : ident) (ck : clock),
      In (x,ck) cenv <-> exists ty, Env.find x env = Some (ty,ck).

  Lemma envs_eq_find :
    forall env cenv x ck,
      envs_eq env cenv ->
      In (x, ck) cenv ->
      find_clock env x = OK ck.
  Proof.
    unfold find_clock, envs_eq. intros * Heq Hin.
    rewrite Heq in Hin. destruct Hin as [? Hfind].
    now rewrite Hfind.
  Qed.

  Lemma l_sem_eq_clock :
   forall G H b x cenv env ck eq ss (* cs *),
     LC.wc_equation G cenv eq ->
     LS.sem_equation G H b eq ->
     envs_eq env cenv ->
     In x (fst eq) ->
     (* TODO: var_inv *)
     LS.sem_var H x ss ->
     (* abstract_clock ss ≡ cs -> *)
     find_clock env x = OK ck ->
     NLSC.sem_clock H b ck (abstract_clock ss).
  Proof.
  Admitted.

  Lemma sem_lexp_step2: forall H b e v s,
      NLSC.sem_lexp H b e (v ::: s) ->
      NLSC.sem_lexp (NLSC.History_tl H) (Streams.tl b) e s.
  Proof.
    induction e; intros * Hsem; inv Hsem.
    - econstructor; eauto. unfold_St b. inv H4. simpl in *. eauto.
    - econstructor; eauto using sem_var_step_nl.
    - inv H9; econstructor; eauto using sem_var_step_nl.
    - inv H8; econstructor; eauto using sem_var_step_nl.
    - inv H10; econstructor; eauto using sem_var_step_nl.
  Qed.

  Lemma sem_cexp_step2: forall H b e v s,
      NLSC.sem_cexp H b e (v ::: s) ->
      NLSC.sem_cexp (NLSC.History_tl H) (Streams.tl b) e s.
  Proof.
    induction e; intros * Hsem; inv Hsem.
    - inv H10; econstructor; eauto using sem_var_step_nl.
    - inv H10; econstructor; eauto using sem_lexp_step2.
    - econstructor; eauto using sem_lexp_step2.
  Qed.

  Lemma fby_const:
    forall b c xs ys rs,
      LS.fby xs ys rs ->
      xs ≡ LS.const c b ->
      b  ≡ abstract_clock rs ->
      rs ≡ NLSC.fby (sem_const c) ys.
  Proof.
    cofix Cofix; intros * Hfby Hconst Hac.
    unfold_Stv ys; inv Hfby; rewrite unfold_Stream in Hac;
      simpl in Hac; rewrite unfold_Stream; simpl; symmetry in Hconst.
    - apply const_inv1 in Hconst.
      destruct Hconst as (?& Hc & Hb). rewrite Hb in Hac.
      inv Hac; simpl in *. econstructor; simpl; eauto.
    - apply const_inv2 in Hconst.
      destruct Hconst as (?& Hc & Hb & Hx). rewrite Hb in Hac.
      inv Hac; simpl in *. econstructor; simpl; eauto.
      clear H Cofix. revert H0 H3 Hb Hc. revert rs0 x0 ys xs0 c0 c b.
      cofix Cofix; intros * Hac Hfby1 Hb Hconst.
      unfold_Stv ys; inv Hfby1; rewrite unfold_Stream in Hac;
        simpl in Hac; rewrite unfold_Stream; simpl; symmetry in Hconst.
      + apply const_inv1 in Hconst.
        destruct Hconst as (?& Hc & Hbb). rewrite Hbb in Hac.
        inv Hac; simpl in *. econstructor; simpl; eauto.
        eapply Cofix; eauto. reflexivity.
      + apply const_inv2 in Hconst.
        destruct Hconst as (?& Hc & Hbb & Hx). rewrite Hbb in Hac.
        inv Hac; simpl in *. econstructor; simpl; eauto.
  Qed.

  Lemma sem_const_exp:
    forall G H b e c c' xs,
      to_constant e = OK c ->
      LS.sem_exp G H b e [present c' ::: xs] ->
      c' = sem_const c.
  Proof.
    induction e using L.exp_ind2; intros * Htoc Hsem;
      inv Htoc; inv Hsem.
    - symmetry in H5. apply const_inv2 in H5. inv H5. tauto.
    - cases. inv H0. inv H5.
      inv H10. inv H6. inv H12. inv H7. rewrite app_nil_r in H0.
      subst. inv H6.
      eapply H4; eauto.
  Qed.

  Lemma fby_const_when :
    forall G H bk x i ck e b c s cs css xs ys,
      LS.sem_var H x xs ->
      NLSC.sem_clock H bk (Con ck i b) (abstract_clock xs) ->
      LS.fby css ys xs ->
      to_constant e = OK c ->
      LS.sem_exp G H bk e [cs] ->
      LS.when b s cs css ->
      xs ≡ NLSC.fby (sem_const c) ys.
  Proof.
    cofix Cofix; intros * Hsemv Hsc Hfby Htoc Hse Hwhen.
    unfold_Stv xs; inv Hfby; rewrite unfold_Stream; simpl;
      rewrite unfold_Stream in Hsc; simpl in Hsc.
    - econstructor; simpl; eauto. destruct cs.
      eapply sem_var_step in Hsemv; eauto.
      assert (Htoc' := Htoc).
      eapply sem_const_step in Htoc; eauto.
      eapply sem_clock_step in Hsc.
      inv Hwhen; eapply Cofix; eauto.
    - econstructor; simpl; eauto. inv Hwhen. f_equal.
      eapply sem_const_exp; eauto. clear Cofix.
      eapply sem_clock_step in Hsc.
      eapply sem_var_step in Hsemv.
      assert (Htoc' := Htoc).
      inv Hwhen. eapply sem_const_step in Htoc'; eauto. clear Hse.
      revert dependent H. revert H3 H5 H6. revert bk xs xs0 xs1 xs0 cs0 ys0 y.
      cofix Cofix; intros.
      unfold_Stv xs; inv H3; rewrite unfold_Stream; simpl;
        rewrite unfold_Stream in Hsc; simpl in Hsc;
          eapply sem_clock_step in Hsc;
          eapply sem_var_step in Hsemv;
          econstructor; simpl; eauto;
            inv H5; eapply Cofix; eauto using sem_const_step.
  Qed.

  Lemma var_fby_const :
    forall G H b c a env cenv ck ckx x e0 e1 cs xs ys,
      LS.sem_exp G H b e0 [cs] ->
      LS.sem_var H x xs ->
      LS.fby cs ys xs ->
      find_clock env x = OK ck ->
      LC.wc_exp G cenv (L.Efby [e0] [e1] a) ->
      [ckx] = map L.ckstream a ->
      In (x, ckx) cenv ->
      envs_eq env cenv ->
      to_constant e0 = OK c ->
      NLSC.sem_clock H b ck (abstract_clock xs) ->
      NLSC.sem_var H x (NLSC.fby (sem_const c) ys).
  Proof.
    destruct ck; intros * Hse Hxs Hfby Hfind Hwc Hckx Hin Henv Htoc Hsc.
    - (* ck = Base. Show that e0 is not EWhen *)
      inv Hsc. destruct e0; inv Htoc.
      + inv Hse. eapply fby_const in Hfby; eauto.
        now rewrite <- Hfby, <- sem_var_var.
      + cases. inv Hwc. inv H5. inv H4. rewrite <- Hckx in H7.
        inv H7. inv H11. destruct tys; inv H4.
        unfold L.ckstream, stripname in Hin. simpl in Hin.
        eapply envs_eq_find with (x := x) in Henv; eauto.
        rewrite Henv in Hfind. discriminate.
    - destruct e0; inv Htoc.
      + inv Hse. eapply fby_const in Hfby; eauto.
        now rewrite <- Hfby, <- sem_var_var.
        apply ac_fby1 in Hfby. symmetry in H5. apply ac_const in H5.
        now rewrite H5, Hfby.
      + cases. eapply envs_eq_find with (x := x) in Henv; eauto.
        rewrite Henv in Hfind. inv Hfind. destruct a; inv Hckx.
        destruct a0; inv H3.
        inv Hwc. inv H5. inv H4. simpl in *.
        rewrite app_nil_r in H7. destruct tys; inv H7.
        destruct tys; inv H16. rewrite <- H2 in H5.
        unfold L.ckstream, stripname in H5. simpl in H5. inv H5.
        (* now (i,b0) = (i0,b1) *)
        inv Hse. inv H18. inv H7. simpl in H20. rewrite app_nil_r in H20.
        inv H20. inv H11.
        assert (Hxs' := Hxs).
        eapply fby_const_when in Hxs; eauto.
        now rewrite <- Hxs, <- sem_var_var.
  Qed.

  Lemma sem_toeq :
    forall tenv cenv G H P env envo eq eq' b,
      LT.wt_equation G tenv eq ->
      LC.wc_equation G cenv eq ->
      envs_eq env cenv ->
      (forall f xs ys,
          LS.sem_node G f xs ys ->
          NLSC.sem_node P f xs ys) ->
      to_equation env envo eq = OK eq' ->
      LS.sem_equation G H b eq ->
      NLSC.sem_equation P H b eq'.
  Proof.
    intros * Hwt Hwc Henv Hsemnode Htoeq Hsem.
    destruct eq as [ xs es ].
    destruct xs as [ | ? [] ].
    - (* no left-hand side *)
      destruct es; inv Htoeq. cases.
      inversion_clear Hsem as [ ????? Hseme Hsemv].
      inversion Hsemv as [Hsv Hss |]. inversion Hseme as [| ???? Hsem [|]].
      rewrite <- concat_nil in Hss. simpl in Hss.
      rewrite app_nil_r in Hss. subst.
      inversion Hsem as [| | | | | | | |???????? Hsemn]. subst.
      inversion Hsemn as [???????? Hf2]. inversion Hf2 as [Hlen|].
      apply (f_equal (@length ident)) in Hlen; simpl in Hlen.
      unfold LS.idents in Hlen. rewrite Coqlib.list_length_map in Hlen.
      pose proof (L.n_outgt0 n). omega.
    - (* single ident *)
      destruct es. inv Htoeq. destruct es; [ idtac | inv Htoeq; cases ].
      revert dependent H.
      revert dependent b.
      einduction e using L.exp_ind2; intros bb HH Hsem.
      (* TODO: all cases except Fby and App are the same *)
      + (* Econst *)
        unfold to_equation in Htoeq. monadInv Htoeq. rename x into ck.
        assert (Hsem' := Hsem).
        inversion_clear Hsem as [ ????? Hseme Hsemv].
        inversion Hseme as [| ????? Hse]. inv Hse. simpl in Hsemv.
        rewrite app_nil_r in Hsemv.
        inversion Hsemv as [|???? Hsvar Hf2]. inv Hf2.
        assert (Hsc := Hwc). eapply l_sem_eq_clock in Hsc; simpl; eauto.
        inversion_clear Hwt as [Hwte ?]. inv Hwte.
        inversion_clear Hwc as [Hwce ?]. inv Hwce.
        eapply sem_exp_cexp in EQ1; eauto.
        apply sem_var_var in Hsvar. econstructor; eauto.
        clear - Hsc EQ1. revert dependent HH. revert bb y0. cofix Cofix; intros.
        unfold_Stv y0; rewrite unfold_Stream in Hsc; simpl in Hsc;
          econstructor; eauto; eapply Cofix;
            eauto using sem_clock_step, sem_cexp_step2.
      + (* Evar *)
        unfold to_equation in Htoeq. monadInv Htoeq. rename x into ck.
        assert (Hsem' := Hsem).
        inversion_clear Hsem as [ ????? Hseme Hsemv].
        inversion Hseme as [| ????? Hse]. inv Hse. simpl in Hsemv.
        rewrite app_nil_r in Hsemv.
        inversion Hsemv as [|???? Hsvar Hf2]. inv Hf2.
        assert (Hsc := Hwc). eapply l_sem_eq_clock in Hsc; simpl; eauto.
        inversion_clear Hwt as [Hwte ?]. inv Hwte.
        inversion_clear Hwc as [Hwce ?]. inv Hwce.
        eapply sem_exp_cexp in EQ1; eauto.
        apply sem_var_var in Hsvar. econstructor; eauto.
        clear - Hsc EQ1. revert dependent HH. revert bb y0. cofix Cofix; intros.
        unfold_Stv y0; rewrite unfold_Stream in Hsc; simpl in Hsc;
          econstructor; eauto; eapply Cofix;
            eauto using sem_clock_step, sem_cexp_step2.
      + (* Eunop *)
        unfold to_equation in Htoeq. monadInv Htoeq. rename x into ck.
        assert (Hsem' := Hsem).
        inversion_clear Hsem as [ ????? Hseme Hsemv].
        inversion Hseme as [| ????? Hse]. inv Hse. simpl in Hsemv.
        rewrite app_nil_r in Hsemv.
        inversion Hsemv as [|???? Hsvar Hf2]. inv Hf2.
        assert (Hsc := Hwc). eapply l_sem_eq_clock in Hsc; simpl; eauto.
        inversion_clear Hwt as [Hwte ?]. inv Hwte.
        inversion_clear Hwc as [Hwce ?]. inv Hwce.
        eapply sem_exp_cexp in EQ1; eauto.
        apply sem_var_var in Hsvar. econstructor; eauto.
        clear - Hsc EQ1. revert dependent HH. revert bb y0. cofix Cofix; intros.
        unfold_Stv y0; rewrite unfold_Stream in Hsc; simpl in Hsc;
          econstructor; eauto; eapply Cofix;
            eauto using sem_clock_step, sem_cexp_step2.
      + (* EBinop *)
        unfold to_equation in Htoeq. monadInv Htoeq. rename x into ck.
        assert (Hsem' := Hsem).
        inversion_clear Hsem as [ ????? Hseme Hsemv].
        inversion Hseme as [| ????? Hse]. inv Hse. simpl in Hsemv.
        rewrite app_nil_r in Hsemv.
        inversion Hsemv as [|???? Hsvar Hf2]. inv Hf2.
        assert (Hsc := Hwc). eapply l_sem_eq_clock in Hsc; simpl; eauto.
        inversion_clear Hwt as [Hwte ?]. inv Hwte.
        inversion_clear Hwc as [Hwce ?]. inv Hwce.
        eapply sem_exp_cexp in EQ1; eauto.
        apply sem_var_var in Hsvar. econstructor; eauto.
        clear - Hsc EQ1. revert dependent HH. revert bb y0. cofix Cofix; intros.
        unfold_Stv y0; rewrite unfold_Stream in Hsc; simpl in Hsc;
          econstructor; eauto; eapply Cofix;
            eauto using sem_clock_step, sem_cexp_step2.
      + (* EFby *)
        inversion Htoeq as [Heq']. cases; monadInv Heq'. rename x1 into ck.
        assert (Hsem' := Hsem).
        inversion_clear Hsem as [ ????? Hseme Hsemv].
        inversion Hseme as [| ???? Hsef Hse]. inv Hse. simpl in Hsemv.
        rewrite app_nil_r in Hsemv.
        inversion Hsemv as [|???? Hsvar Hf2]. inv Hf2.
        assert (Hsc := Hwc). eapply l_sem_eq_clock in Hsc; simpl; eauto.
        inversion_clear Hwc as [Hwce ?]. inv Hwce.
        inversion_clear Hwt as [Hwte ?]. inversion Hwte as [|?? Hwt].
        inversion Hwt as [| | | | ? ? ? ? Hwte1 | | | |]. inv Hwte1.
        inversion Hsef as [| | | |???????? Hse0 Hse1 Hwfby | | | |].
        inversion Hse1 as [|????? Hf2]. inv Hf2.
        inversion Hwfby as [|?????? Hlsf Hf Hcat]. inv Hf. rewrite app_nil_r in *.
        subst. eapply sem_exp_lexp in EQ2; eauto.
        econstructor; eauto. instantiate (1 := y1).
        apply ac_fby2 in Hlsf. rewrite <- Hlsf in Hsc.
        clear - Hsc EQ2. revert dependent HH. revert bb y1. cofix Cofix; intros.
        unfold_Stv y1; rewrite unfold_Stream in Hsc; simpl in Hsc; auto;
          econstructor; eauto; eapply Cofix;
            eauto using sem_clock_step, sem_lexp_step2.
        (* we show how to erase Whens in constants using var_fby_const *)
        inversion Hse0 as [| ????? Hf2]. inv Hf2.
        inversion Hcat as [Hx1]. rewrite app_nil_r in Hx1. subst.
        destruct H1 as (Hwf & HliftO & HFin).
        inversion HFin as [|?????  Hf2 Huseless Hnil].
        inv Hf2. rewrite app_nil_r in Hnil.
        eapply var_fby_const; eauto.
      + (* EWhen *)
        unfold to_equation in Htoeq. monadInv Htoeq. rename x into ck.
        assert (Hsem' := Hsem).
        inversion_clear Hsem as [ ????? Hseme Hsemv].
        inversion Hseme as [| ????? Hse]. inv Hse. simpl in Hsemv.
        rewrite app_nil_r in Hsemv.
        inversion Hsemv as [|???? Hsvar Hf2]. inv Hf2.
        assert (Hsc := Hwc). eapply l_sem_eq_clock in Hsc; simpl; eauto.
        inversion_clear Hwt as [Hwte ?]. inv Hwte.
        inversion_clear Hwc as [Hwce ?]. inv Hwce.
        eapply sem_exp_cexp in EQ1; eauto.
        apply sem_var_var in Hsvar. econstructor; eauto.
        clear - Hsc EQ1. revert dependent HH. revert bb y0. cofix Cofix; intros.
        unfold_Stv y0; rewrite unfold_Stream in Hsc; simpl in Hsc;
          econstructor; eauto; eapply Cofix;
            eauto using sem_clock_step, sem_cexp_step2.
      + (* EMerge *)
        unfold to_equation in Htoeq. monadInv Htoeq. rename x into ck.
        assert (Hsem' := Hsem).
        inversion_clear Hsem as [ ????? Hseme Hsemv].
        inversion Hseme as [| ????? Hse]. inv Hse. simpl in Hsemv.
        rewrite app_nil_r in Hsemv.
        inversion Hsemv as [|???? Hsvar Hf2]. inv Hf2.
        assert (Hsc := Hwc). eapply l_sem_eq_clock in Hsc; simpl; eauto.
        inversion_clear Hwt as [Hwte ?]. inv Hwte.
        inversion_clear Hwc as [Hwce ?]. inv Hwce.
        eapply sem_exp_cexp in EQ1; eauto.
        apply sem_var_var in Hsvar. econstructor; eauto.
        clear - Hsc EQ1. revert dependent HH. revert bb y0. cofix Cofix; intros.
        unfold_Stv y0; rewrite unfold_Stream in Hsc; simpl in Hsc;
          econstructor; eauto; eapply Cofix;
            eauto using sem_clock_step, sem_cexp_step2.
      + (* Eite *)
        unfold to_equation in Htoeq. monadInv Htoeq. rename x into ck.
        assert (Hsem' := Hsem).
        inversion_clear Hsem as [ ????? Hseme Hsemv].
        inversion Hseme as [| ????? Hse]. inv Hse. simpl in Hsemv.
        rewrite app_nil_r in Hsemv.
        inversion Hsemv as [|???? Hsvar Hf2]. inv Hf2.
        assert (Hsc := Hwc). eapply l_sem_eq_clock in Hsc; simpl; eauto.
        inversion_clear Hwt as [Hwte ?]. inv Hwte.
        inversion_clear Hwc as [Hwce ?]. inv Hwce.
        eapply sem_exp_cexp in EQ1; eauto.
        apply sem_var_var in Hsvar. econstructor; eauto.
        clear - Hsc EQ1. revert dependent HH. revert bb y0. cofix Cofix; intros.
        unfold_Stv y0; rewrite unfold_Stream in Hsc; simpl in Hsc;
          econstructor; eauto; eapply Cofix;
            eauto using sem_clock_step, sem_cexp_step2.
      + (* EApp *)
        unfold to_equation in Htoeq. monadInv Htoeq. rename x into ck.
        assert (Hsem' := Hsem).
        inversion_clear Hsem as [ ????? Hseme Hsemv].
        inversion Hseme as [| ???? Hsea Hse]. inv Hse. simpl in Hsemv.
        rewrite app_nil_r in Hsemv.
        inversion Hsemv as [|???? Hsvar Hf2]. inv Hf2.
        assert (Hsc := Hwc). inversion EQ as [Hf]. monadInv Hf.
        rename x into ck.
        eapply l_sem_eq_clock in Hsc; eauto; [| simpl; now left].
        inversion_clear Hwt as [Hwte ?]. inversion Hwte as [| ?? Hwt]. inv Hwt.
        inv Hsea. apply sem_var_var in Hsvar.
        econstructor; eauto using  sem_exps_lexps.
        admit.
  Admitted.

  Lemma sem_toeqs :
    forall tenv cenv G H P env envo eqs eqs' b,
      Forall (LT.wt_equation G tenv) eqs ->
      Forall (LC.wc_equation G cenv) eqs ->
      envs_eq env cenv ->
      (forall f xs ys,
          LS.sem_node G f xs ys ->
          NLSC.sem_node P f xs ys) ->
      mmap (to_equation env envo) eqs = OK eqs' ->
      Forall (LS.sem_equation G H b) eqs ->
      Forall (NLSC.sem_equation P H b) eqs'.
  Proof.

    intros * Hwt Hwc Henv Hnode Hmmap Hsem. revert dependent eqs'.
    induction Hsem; intros. now inv Hmmap. apply mmap_cons in Hmmap.
    destruct Hmmap as (eq' & leq' & Heqs' & Htoeq & Hmmap). subst.
    inv Hwt. inv Hwc.
    constructor. eapply sem_toeq; eauto.
    apply IHHsem; auto.
  Qed.


  (* TODO: move to CommonList *)
  Lemma in_app_comm :
    forall  {A : Type} (a : A) (l1 l2 : list A), In a (l1 ++ l2) <-> In a (l2 ++ l1).
  Proof.
    intros; split; intro Hin; apply in_app_or in Hin;
      apply in_or_app; tauto.
  Qed.

  Lemma envs_eq_app_comm :
    forall env (xs ys : list (ident * (type * clock))),
      envs_eq env (idck (xs ++ ys))
      <-> envs_eq env (idck (ys ++ xs)).
  Proof.
    split; unfold envs_eq; intros Heq x ck; split; intro Hin;
      try (rewrite idck_app in Hin;
           apply in_app_comm in Hin; apply Heq; now rewrite idck_app);
      try (rewrite idck_app; rewrite in_app_comm; rewrite <- idck_app;
           now apply Heq).
  Qed.

  (* TODO: move to Environment *)
  Lemma env_find_env_from_list':
    forall {A} x (v: A) xs s,
      Env.find x (Env.adds' xs s) = Some v
      -> In (x, v) xs \/ (~InMembers x xs /\ Env.find x s = Some v).
  Proof.
    induction xs as [|(x', v') xs IH]; simpl. now intuition.
    intros s Hfind. apply IH in Hfind as [|(Hnim & Hfind)]; auto.
    destruct (ident_eq_dec x' x).
    + subst. rewrite Env.gss in Hfind.
      injection Hfind. intro; subst; auto.
    + rewrite Env.gso in Hfind; intuition.
  Qed.

  Lemma env_eq_env_from_list:
    forall xs,
      NoDupMembers xs ->
      envs_eq (Env.from_list xs) (idck xs).
  Proof.
    intros xs Hnodup x ck. split.
    - unfold idck. rewrite in_map_iff.
      intro Hxs. destruct Hxs as (y & Hx & Hin). inv Hx.
      exists (fst (snd y)).
      apply Env.In_find_adds'; auto.
      destruct y as [? [? ?]]. auto.
    - intro Hfind. destruct Hfind as [ty Hfind].
      apply Env.from_list_find_In in Hfind.
      unfold idck. rewrite in_map_iff. exists (x,(ty,ck)). simpl. tauto.
  Qed.

  Lemma env_eq_env_adds':
    forall s xs ys,
      NoDupMembers (xs ++ ys) ->
      envs_eq s (idck ys) ->
      envs_eq (Env.adds' xs s) (idck (xs ++ ys)).
  Proof.
    intros s xs ys Hnodup Heq x ck. split.
    - rewrite idck_app. rewrite in_app_iff. destruct 1 as [Hin | Hin].
      unfold idck in Hin. rewrite in_map_iff in Hin.
      destruct Hin as (y & Hx & Hin). inv Hx. exists (fst (snd y)).
      apply Env.In_find_adds'; auto.
      now apply NoDupMembers_app_l in Hnodup.
      destruct y as (? & ? & ?). now simpl.
      assert (Hin' := Hin).
      apply Heq in Hin. destruct Hin as [ty Hin].
      exists ty. rewrite <- Hin. apply Env.gsso'.
      apply In_InMembers in Hin'. rewrite InMembers_idck in Hin'.
      eapply NoDupMembers_app_InMembers; eauto.
      now rewrite Permutation_app_comm.
    - destruct 1 as [ty Hfind].
      apply env_find_env_from_list' in Hfind.
      destruct Hfind as [Hin | [Hin Hfind]];
        rewrite idck_app; apply in_app_iff.
      left. rewrite In_idck_exists. eauto.
      right. unfold envs_eq in Heq. rewrite Heq. eauto.
  Qed.

  Lemma envs_eq_node (n : L.node) :
    envs_eq
      (Env.adds' (L.n_vars n)
                 (Env.adds' (L.n_in n)
                            (Env.from_list (L.n_out n))))
      (idck (L.n_in n ++ L.n_vars n ++ L.n_out n)).
  Proof.
    rewrite envs_eq_app_comm.
    rewrite <- app_assoc.
    apply env_eq_env_adds'. rewrite app_assoc.
    rewrite Permutation_app_comm. exact (L.n_nodup n).
    rewrite envs_eq_app_comm.
    apply env_eq_env_adds'. assert (Hnodup := L.n_nodup n).
    rewrite Permutation_app_comm in Hnodup.
    rewrite <- app_assoc in Hnodup. apply NoDupMembers_app_r in Hnodup.
    now rewrite Permutation_app_comm.
    apply env_eq_env_from_list. assert (Hnodup := L.n_nodup n).
    now apply NoDupMembers_app_r, NoDupMembers_app_r in Hnodup.
  Qed.

  Lemma inin_l_nl :
    forall f n n',
      to_node n = OK n' ->
      Ord.Is_node_in f (NL.n_eqs n') ->
      Lord.Is_node_in f (L.n_eqs n).
  Proof.
    intros * Htr Hord.
    destruct n'. simpl in Hord.
    tonodeInv Htr.
    clear - Hord Hmmap. revert dependent n_eqs.
    induction (L.n_eqs n); intros. inv Hmmap. inv Hord.
    apply mmap_cons in Hmmap.
    destruct Hmmap as (eq' & l' & Hneqs & Hteq & Hmmap); subst.
    inversion_clear Hord as [ ? ? Hord' |].
    - econstructor.
      destruct eq' as [| i ck x le |]; inv Hord'.
      destruct a as [ xs [|]]. inv Hteq. cases.
      destruct l0; [ idtac | inv Hteq; cases ].
      destruct e; inv Hteq; cases; monadInv H0;
        econstructor; apply Lord.INEapp2.
    - apply Exists_cons_tl. eapply IHl; eauto.
  Qed.

  Lemma ninin_l_nl :
    forall f n n',
      to_node n = OK n' ->
      ~ Lord.Is_node_in f (L.n_eqs n) ->
      ~ Ord.Is_node_in f (NL.n_eqs n').
  Proof.
    intros. intro. destruct H0. eapply inin_l_nl; eauto.
  Qed.

  Lemma ord_l_nl :
    forall G P,
      to_global G = OK P ->
      Lord.Ordered_nodes G ->
      Ord.Ordered_nodes P.
  Proof.
    intros * Htr Hord.
    revert dependent P.
    induction Hord; intros. inv Htr. constructor.
    apply mmap_cons in Htr.
    destruct Htr as (n' & P' & HP & Hton & Hmmap). subst.
    constructor; auto.
    - intros f Hin.
      assert (Lord.Is_node_in f (L.n_eqs nd)) as Hfin.
      eapply inin_l_nl; eauto.
      apply H in Hfin. destruct Hfin as [ Hf Hnds ].
      split.
      apply to_node_name in Hton. now rewrite <- Hton.
      clear - Hnds Hmmap. revert dependent P'.
      induction nds; intros; inv Hnds;
        apply mmap_cons in Hmmap;
        destruct Hmmap as (n'' & P'' & HP & Hton' & Hmmap); subst.
      constructor. now apply to_node_name.
      apply Exists_cons_tl. apply IHnds; auto.
    - apply to_node_name in Hton. rewrite <- Hton.
      monadInv Hmmap. clear - H0 H1.
      induction H1; eauto. inv H0.
      constructor. apply to_node_name in H. now rewrite <- H.
      now apply IHlist_forall2.
  Qed.

  Lemma clocks_of_sclocksof :
    forall ins, NLSC.clocks_of ins = LS.sclocksof ins.
  Proof.
    reflexivity.
  Qed.


  Theorem sem_l_nl :
    forall G P f ins outs,
      Lord.Ordered_nodes G ->
      LT.wt_global G ->
      LC.wc_global G ->
      to_global G = OK P ->
      (LS.sem_node G f ins outs -> NLSC.sem_node P f ins outs).
  Proof.
    induction G as [|node]. now inversion 5.
    intros * Hord Hwt Hwc Htr Hsem.
    assert (Hsem' := Hsem).
    inversion_clear Hsem' as [? ? ? ? ? ? Hfind Hins Houts Heqs Hbk].
    pose proof (Lord.find_node_not_Is_node_in _ _ _ Hord Hfind) as Hnini.
    inv Hwt. inv Hwc.
    simpl in Hfind. destruct (ident_eqb (L.n_name node) f) eqn:Hnf.
    - assert (Hord':=Hord).
      inversion_clear Hord as [|? ? Hord'' Hnneqs Hnn].
      injection Hfind; intro HR; rewrite HR in *; clear HR; simpl in *.
      eapply LS.Forall_sem_equation_global_tl in Heqs; eauto.
      assert (Htr' := Htr). apply mmap_cons in Htr'.
      destruct Htr' as (n' & P' & Hp & Htrn & Hmmap). subst.
      assert (forall f ins outs,
                 LS.sem_node G f ins outs
                 -> NLSC.sem_node P' f ins outs) as IHG'
          by auto.
      apply ident_eqb_eq in Hnf. rewrite <- Hnf.
      inversion H3 as (Hwt1 & Hwt2 & Hwt3 & Hwt4).
      inversion H6 as (Hwc1 & Hwc2 & Hwc3 & Hwc4).
      econstructor; simpl.
      + tonodeInv Htrn. rewrite ident_eqb_refl; eauto.
      + tonodeInv Htrn. simpl.
        eapply Forall2_impl_In in Hins; eauto.
        intros * Hina Hinb0 Hsemv.
        eapply sem_var_var. eauto.
      + tonodeInv Htrn. simpl. eapply Forall2_impl_In in Houts; eauto.
        intros * Hina Hinb0 Hsemv. eapply sem_var_var. eauto.
      + assert (b ≡ NLSC.clocks_of ins) as Hb
            by (now rewrite clocks_of_sclocksof).
        rewrite <- Hb.
        admit. (* same_clock *)
      + rewrite clocks_of_sclocksof.
        apply NLSC.sem_equation_cons2; auto.
        eapply ord_l_nl; eauto.
        assert (Hton := Htrn). tonodeInv Htrn. simpl in *.
        eapply sem_toeqs; eauto.
        apply envs_eq_node.
        apply Forall_forall; intros.
        eapply Forall_forall in Heqs; eauto.
        now rewrite <- Hbk.
        assert (Htrn' := Htrn).
        apply to_node_name in Htrn. rewrite <- Htrn.
        eapply ninin_l_nl; eauto.
  - apply ident_eqb_neq in Hnf.
    eapply LS.sem_node_cons in Hsem; auto.
    assert (Htr' := Htr).
    apply mmap_cons in Htr.
    destruct Htr as (n' & P' & Hp & Htn & Hmmap). subst.
    rewrite cons_is_app in Hord.
    apply Lord.Ordered_nodes_append in Hord.
    eapply NLSC.sem_node_cons2; eauto.
    eapply ord_l_nl; eauto. apply to_node_name in Htn. rewrite <- Htn.
    monadInv Hmmap. clear - H0 H7.
    induction H0; eauto. inv H7.
    constructor. apply to_node_name in H. now rewrite <- H.
    now apply IHlist_forall2.
  Admitted.

End LUSTRE_TO_NLUSTRE.

Module LustreToNLustreFun
       (Ids   : IDS)
       (Op    : OPERATORS)
       (OpAux : OPERATORS_AUX Op)
       (L     : LSYNTAX  Ids Op)
       (CE    : CESYNTAX     Op)
       (NL    : NLSYNTAX Ids Op CE)
       (LT    : LTYPING  Ids Op L)
       (LC    : LCLOCKING Ids Op L)
       (Ord   : NLORDERED Ids Op CE     NL)
       (Lord  : LORDERED   Ids Op       L)
       (LS    : LSEMANTICS Ids Op OpAux L Lord)
       (NLSC  : NLSEMANTICSCOIND Ids Op OpAux CE NL Ord)
       <: LUSTRE_TO_NLUSTRE Ids Op OpAux L CE NL LT LC Ord Lord LS NLSC.
  Include LUSTRE_TO_NLUSTRE Ids Op OpAux L CE NL LT LC Ord Lord LS NLSC.
End LustreToNLustreFun.
