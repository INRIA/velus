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
       (NLSC        : NLSEMANTICSCOIND Ids Op OpAux CE NL).

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

  Definition to_node (n : L.node) : res NL.node.
    refine (
        let envo := Env.from_list n.(L.n_out) in
        let env := Env.adds' n.(L.n_vars) (Env.adds' n.(L.n_in) envo) in
        let is_not_out :=
            fun x => if Env.mem x envo
                  then Error (msg "output variable defined as a fby")
                  else OK tt in
        match mmap_to_equation env is_not_out n with
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
        end).

  (* NL.n_defd obligation *)
  {
    assert (NL.vars_defined neqs = L.vars_defined (L.n_eqs n)).
    { revert neqs P. induction (L.n_eqs n); simpl.
    - intros neqs Htr. inv Htr. auto.
    - intros neqs Htoeq. monadInv Htoeq.
      apply IHl in EQ1. simpl.
      apply ok_fst_defined in EQ. rewrite EQ1. now rewrite <- EQ.
      eauto.
    }
    rewrite H.
    exact (L.n_defd n).
  }

  (* NL.n_vout obligation *)
  {
    intros xo Hin.
    monadInv P. induction H as [| eq leq eq' leq' Htoeq ].
    intro Hbad. inv Hbad.
    assert (Hmmap := P).
    apply mmap_cons2 in P.
    destruct P as (eq'' & leq'' & Heqs' & Htoeq' & Hmmap').
    inv Heqs'.
    simpl. destruct (NL.is_fby eq') eqn:?.
    - unfold NL.vars_defined, flat_map. simpl. rewrite in_app.
      intro Hi. destruct Hi.
      + unfold to_equation in Htoeq. destruct eq''.
        cases; monadInv Htoeq; inv Heqb. simpl in H0. destruct H0; auto. subst.
        unfold is_not_out in EQ. cases_eqn EQ. inv EQ.
        apply Env.Props.P.F.not_mem_in_iff in EQ3. unfold envo in EQ3.
        apply EQ3.
        rewrite in_map_iff in Hin.
        destruct Hin as ((x & ?) & Hfst & Hin). inv Hfst.
        eapply Env.find_In. eapply Env.In_find_adds'; simpl; eauto.
        destruct n. simpl. assert (Hnodup := n_nodup).
        now repeat apply NoDupMembers_app_r in Hnodup.
      + apply IHlist_forall2; auto. exists leq'; auto.
    - apply IHlist_forall2. exists leq'; auto. assumption.
  }

  (* NL.n_good obligation *)
  {
    Axiom AXIOM_VALID_TODO_REMOVE_ME :
      forall id, valid id.
    repeat split.
    - apply Forall_Forall. exact n.(L.n_good).
      (* TODO: valid in, vars, vars *)
      apply Forall_forall; intros; apply AXIOM_VALID_TODO_REMOVE_ME.
    - (* TODO: valid n_name *)
      apply AXIOM_VALID_TODO_REMOVE_ME.
  }

  Defined. (* to_node *)

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
    (* intro Htr. tonodeInv Htr. auto. *)
    (* Qed. *)
  Admitted.

  Lemma to_node_in n n' :
    to_node n = OK n' -> (LS.idents (L.n_in n)) = (NLSC.idents (NL.n_in n')).
  Proof.
    (* intro Htr. tonodeInv Htr. auto. *)
    (* Qed. *)
  Admitted.

  Lemma to_node_out n n' :
    to_node n = OK n' -> (LS.idents (L.n_out n)) = (NLSC.idents (NL.n_out n')).
  Proof.
    (* intro Htr. tonodeInv Htr. auto. *)
    (* Qed. *)
  Admitted.


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

  Lemma ac_fby :
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
       (NLSC  : NLSEMANTICSCOIND Ids Op OpAux CE NL)
       <: LUSTRE_TO_NLUSTRE Ids Op OpAux L CE NL LT LC Ord Lord LS NLSC.
  Include LUSTRE_TO_NLUSTRE Ids Op OpAux L CE NL LT LC Ord Lord LS NLSC.
End LustreToNLustreFun.
