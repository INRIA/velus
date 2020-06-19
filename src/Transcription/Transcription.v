From Velus Require Import Common.
From Velus Require Import Environment.
From Velus Require Import Operators.
From Velus Require Import Clocks.
From Velus Require Import Lustre.LSyntax.
From Velus Require Import CoreExpr.CESyntax.
From Velus Require Import NLustre.NLSyntax.

From Coq Require Import Omega.
From Coq Require Import Permutation.
From Coq Require Import String.

From Coq Require Import List.
Import List.ListNotations.

From compcert Require Import common.Errors.
Open Scope error_monad_scope.

(** * Turn a normalized Lustre program into an NLustre program *)

(** Transcription algorithm and common lemmas for Correctness,
    Typing and Clocking preservation *)

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
    let (xs, es) := eq in
    match es with
    | [e] =>
      match e with
      | L.Eapp f es None _ =>
        do les <- mmap to_lexp es;
        OK (NL.EqApp xs (find_base_clock (L.clocksof es)) f les None)
      | L.Eapp f es (Some (L.Evar x (_, (ckx, _)))) _ => (* use clock annot or lookup? *)
        do les <- mmap to_lexp es;
        OK (NL.EqApp xs (find_base_clock (L.clocksof es)) f les (Some (x, ckx)))
      | L.Eapp f es (Some _) _ => Error (msg "reset equation not normalized")
      | L.Efby [e0] [e] _ =>
        match xs with
          | [x] =>
            do _  <- envo x;
            do c0 <- to_constant e0;
            do ck <- find_clock env x;
            do le <- to_lexp e;
            OK (NL.EqFby x ck c0 le)
          | _ => Error (msg "fby equation not normalized")
        end
      | _ =>
        match xs with
        | [x] =>
          do ck <- find_clock env x;
          do ce <- to_cexp e;
          OK (NL.EqDef x ck ce)
        | _ => Error (msg "basic equation not normalized")
        end
      end
    | _ => Error (msg "equation not normalized")
    end.

    (* match eq with *)
    (* | (xs, [L.Eapp f es None _]) => *)
    (*     do les <- mmap to_lexp es; *)
    (*     OK (NL.EqApp xs (find_base_clock (L.clocksof es)) f les None) *)

    (* | (xs, [L.Eapp f es (Some (L.Evar x _)) _]) => *)
    (*     do les <- mmap to_lexp es; *)
    (*     OK (NL.EqApp xs (find_base_clock (L.clocksof es)) f les (Some x)) *)

    (* | ([x], [L.Efby [e0] [e] _]) => *)
    (*     do _  <- envo x; *)
    (*     do c0 <- to_constant e0; *)
    (*     do ck <- find_clock env x; *)
    (*     do le <- to_lexp e; *)
    (*     OK (NL.EqFby x ck c0 le) *)

    (* | ([x], [e]) => *)
    (*     do ck <- find_clock env x; *)
    (*     do ce <- to_cexp e; *)
    (*     OK (NL.EqDef x ck ce) *)

    (* | _ => Error (msg "equation not normalized") *)
    (* end. *)

  Lemma find_clock_in_env :
    forall x env ty ck,
      Env.find x env = Some (ty, ck) ->
      find_clock env x = OK ck.
  Proof.
    intros * H. unfold find_clock. now rewrite H.
  Qed.

  Lemma find_clock_out : forall n x ty ck,
      In (x, (ty, ck)) (L.n_out n) ->
      find_clock
        (Env.adds' (L.n_vars n)
                   (Env.adds' (L.n_in n) (Env.from_list (L.n_out n)))
        ) x = OK ck.
  Proof.
    intros * Hin.
    unfold Env.from_list. eapply find_clock_in_env.
    apply In_InMembers in Hin as Hinm.
    pose proof (L.n_nodup n) as Hnodup.
    rewrite 2 Env.gsso'. apply Env.In_find_adds'; eauto.
    - eapply NoDupMembers_app_r, NoDupMembers_app_r, NoDupMembers_app_l in Hnodup; eauto.
    - eapply NoDupMembers_app_InMembers_l; eauto.
      repeat rewrite InMembers_app; auto.
    - eapply NoDupMembers_app_r in Hnodup.
      eapply NoDupMembers_app_InMembers_l; eauto.
      rewrite InMembers_app; auto.
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
          NL.n_nodup    := _;
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
        apply NoDupMembers_app_r, NoDupMembers_app_r, NoDupMembers_app_l in Hnodup; auto.
      + apply IHlist_forall2; auto.
    - apply IHlist_forall2; eauto.
  Qed.

  Next Obligation.
    specialize (L.n_nodup n) as Hndup.
    repeat rewrite app_assoc in *. apply NoDupMembers_app_l in Hndup; auto.
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

  Section Envs_eq.

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
      rewrite Permutation_app_comm. specialize (L.n_nodup n) as Hnd.
      repeat rewrite app_assoc in *. apply NoDupMembers_app_l in Hnd; auto.
      rewrite envs_eq_app_comm.
      apply env_eq_env_adds'. assert (Hnodup := L.n_nodup n).
      repeat rewrite app_assoc in Hnodup. apply NoDupMembers_app_l in Hnodup. rewrite <- app_assoc in Hnodup.
      rewrite Permutation_app_comm in Hnodup.
      rewrite <- app_assoc in Hnodup. apply NoDupMembers_app_r in Hnodup.
      now rewrite Permutation_app_comm.
      apply env_eq_env_from_list. assert (Hnodup := L.n_nodup n).
      now apply NoDupMembers_app_r, NoDupMembers_app_r, NoDupMembers_app_l in Hnodup.
    Qed.

  End Envs_eq.

  Section Clock_operations.

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

    Lemma common_suffix_app :
      forall l l1 l2,
        common_suffix (l ++ l1) (l ++ l2) = l ++ common_suffix l1 l2.
    Proof.
      induction l; simpl; auto.
      intros. cases_eqn HH. now f_equal.
      now rewrite equiv_decb_refl, Pos.eqb_refl in HH0.
    Qed.

    Lemma common_suffix_app_l :
      forall l l1 l2,
        length l2 < length l1 ->
        common_suffix l1 l2 = common_suffix (l1 ++ l) l2.
    Proof.
      induction l1; simpl; intros * Hlen.
      - inv Hlen.
      - cases_eqn HH. f_equal. apply IHl1. simpl in Hlen. omega.
    Qed.

    Lemma clock_parent_length :
      forall ck ck',
        clock_parent ck ck' ->
        length (suffix_of_clock ck []) < length (suffix_of_clock ck' []).
    Proof.
      induction 1; simpl;
        setoid_rewrite <- app_nil_l at 4;
        setoid_rewrite suffix_of_clock_app;
        rewrite app_length; simpl; omega.
    Qed.

    Lemma parent_common_suffix :
      forall ck ck',
        clock_parent ck ck' ->
        common_suffix (suffix_of_clock ck' []) (suffix_of_clock ck []) =
        suffix_of_clock ck [].
    Proof.
      induction 1; simpl; setoid_rewrite <- app_nil_l at 3.
      - setoid_rewrite <- app_nil_r at 7.
        rewrite suffix_of_clock_app.
        rewrite common_suffix_app. simpl. now rewrite app_nil_r.
      - rewrite suffix_of_clock_app, <- common_suffix_app_l; auto.
        now apply clock_parent_length.
    Qed.

    Lemma common_suffix_id :
      forall sfx, common_suffix sfx sfx = sfx.
    Proof.
      induction sfx as [| []]; simpl. auto. rewrite IHsfx.
      rewrite equiv_decb_refl, Pos.eqb_refl. now simpl.
    Qed.

    Lemma common_suffix_comm :
      forall sfx1 sfx2, common_suffix sfx1 sfx2 = common_suffix sfx2 sfx1.
    Proof.
      induction sfx1 as [| [i1 b1]], sfx2 as [| [i2 b2]]; simpl; auto.
      cases_eqn EQ.
      - apply andb_prop in EQ as [H].
        apply Peqb_true_eq in H. subst.
        Coq.Bool.Bool.destr_bool; f_equal; auto; f_equal.
      -  apply andb_prop in EQ as [H].
         apply Peqb_true_eq in H. subst.
         apply Bool.andb_false_iff in EQ0 as [];
           Coq.Bool.Bool.destr_bool; now rewrite Pos.eqb_refl in H.
      -  apply andb_prop in EQ0 as [H].
         apply Peqb_true_eq in H. subst.
         apply Bool.andb_false_iff in EQ as [];
           Coq.Bool.Bool.destr_bool; now rewrite Pos.eqb_refl in H.
    Qed.

    Inductive prefix {A} : list A -> list A -> Prop :=
    | prefixNil: forall (l: list A), prefix nil l
    | prefixCons: forall (a: A)(l m:list A), prefix l m -> prefix (a::l) (a::m).
    Hint Constructors prefix.

    Lemma prefix_app:
      forall {A} (l l' : list A), prefix l (l ++ l').
    Proof.
      induction l; simpl; auto.
    Qed.

    Lemma prefix_app':
      forall {A} (l l1 l2 : list A), prefix l l1 -> prefix l (l1 ++ l2).
    Proof.
      induction 1; simpl; auto.
    Qed.

    Lemma prefix_refl :
      forall {A} (l : list A), prefix l l.
    Proof. induction l; auto. Qed.

    Lemma prefix_app3 :
      forall {A} (l1 l2 : list A) e,
        prefix l1 (l2 ++ [e]) ->
        prefix l1 l2 \/ l1 = (l2 ++ [e]).
    Proof.
      intros * Hp. revert dependent l1.
      induction l2; simpl; intros.
      - inv Hp; auto. inv H1; auto.
      - inv Hp; auto. specialize (IHl2 _ H1) as []; auto.
        right. now f_equal.
    Qed.

    Lemma suffix_of_clock_Con:
      forall ck i b,
        suffix_of_clock (Con ck i b) [] =
        suffix_of_clock ck [(i, b)].
    Proof. auto. Qed.

    Lemma suffix_of_clock_inj :
      forall ck ck',
        suffix_of_clock ck [] = suffix_of_clock ck' [] ->
        ck = ck'.
    Proof.
      induction ck, ck'; simpl; auto; intros * Hs.
      - setoid_rewrite <- app_nil_l in Hs at 3.
        rewrite suffix_of_clock_app in Hs.
        now apply app_cons_not_nil in Hs.
      - setoid_rewrite <- app_nil_l in Hs at 2.
        rewrite suffix_of_clock_app in Hs.
        symmetry in Hs. now apply app_cons_not_nil in Hs.
      - setoid_rewrite <- app_nil_l in Hs at 2.
        symmetry in Hs. setoid_rewrite <- app_nil_l in Hs at 2. symmetry in Hs.
        rewrite 2 suffix_of_clock_app in Hs.
        apply app_inj_tail in Hs as [He Hp]. inv Hp.
        specialize (IHck _ He). now subst.
    Qed.

    Lemma prefix_parent :
      forall bk ck,
        ck = bk \/ clock_parent bk ck <->
        prefix (suffix_of_clock bk []) (suffix_of_clock ck []).
    Proof.
      split.
      - destruct 1 as [|H]. subst. apply prefix_refl.
        induction H; simpl.
        + setoid_rewrite <- app_nil_l at 4.
          rewrite suffix_of_clock_app. apply prefix_app.
        + setoid_rewrite <- app_nil_l at 4.
          rewrite suffix_of_clock_app. now apply prefix_app'.
      - intro Hp. revert dependent bk.
        induction ck; intros.
        + simpl in *. inv Hp. destruct bk; simpl in *; auto.
          setoid_rewrite <- app_nil_l in H0 at 3.
          rewrite suffix_of_clock_app in H0.
          now apply app_cons_not_nil in H0.
        + simpl in *.
          setoid_rewrite <- app_nil_l in Hp at 4.
          rewrite suffix_of_clock_app in Hp.
          apply prefix_app3 in Hp as [Hp|Heq].
          specialize (IHck _ Hp) as []; subst; auto.
          rewrite <- suffix_of_clock_app in Heq.
          rewrite app_nil_l, <- suffix_of_clock_Con in Heq.
          apply suffix_of_clock_inj in Heq. subst. auto.
    Qed.

    Lemma prefix_common_suffix :
      forall sfx1 sfx2 p,
        prefix p sfx1 ->
        prefix p sfx2 ->
        prefix p (common_suffix sfx1 sfx2).
    Proof.
      intros. revert dependent sfx2.
      induction H as [|a]. auto. intros * Hp. simpl. destruct a.
      destruct sfx2. inv Hp. destruct p. inv Hp.
      rewrite equiv_decb_refl, Pos.eqb_refl. simpl. constructor. auto.
    Qed.

    Lemma suffix_of_clock_of_suffix :
      forall sfx, sfx = suffix_of_clock (clock_of_suffix sfx Cbase) [].
    Proof.
      intro sfx.
      assert (suffix_of_clock Cbase [] = []) by auto.
      rewrite <- app_nil_l, <- H at 1.
      generalize Cbase.
      induction sfx as [|[i b]]. simpl in *; auto.
      now setoid_rewrite app_nil_r.
      simpl in *. setoid_rewrite <- IHsfx.
      setoid_rewrite <- suffix_of_clock_app. setoid_rewrite app_nil_l at 2.
      now simpl.
    Qed.

    Lemma Tim :
      forall bk ck ck',
        clock_parent bk ck ->
        clock_parent bk ck' ->
        exists d, (d = bk \/ clock_parent bk d) /\
             suffix_of_clock d [] =
             common_suffix (suffix_of_clock ck []) (suffix_of_clock ck' []).
    Proof.
      intros * Hp Hp'.
      eapply or_intror in Hp. apply prefix_parent in Hp.
      eapply or_intror in Hp'. apply prefix_parent in Hp'.
      pose proof (prefix_common_suffix _ _ _ Hp Hp') as Hc.
      rewrite suffix_of_clock_of_suffix in Hc.
      apply prefix_parent in Hc.
      esplit. split; eauto using suffix_of_clock_of_suffix.
    Qed.

    Lemma find_base_clock_bck:
      forall lck bk,
        In bk lck ->
        Forall (fun ck => ck = bk \/ clock_parent bk ck) lck ->
        find_base_clock lck = bk.
    Proof.
      destruct lck. inversion 1.
      simpl. intros * Hin Hf. rewrite <- fold_left_map.
      apply Forall_cons2 in Hf as [Hf1 Hf2].
      revert dependent c. induction lck. simpl. intros.
      inv Hin; try tauto.
      now rewrite clock_of_suffix_of_clock.
      simpl. apply Forall_cons2 in Hf2 as [? Hf]. specialize (IHlck Hf).
      intros. destruct H, Hf1; subst.
      - rewrite common_suffix_id. eauto.
      - rewrite parent_common_suffix; eauto.
      - rewrite common_suffix_comm, parent_common_suffix; eauto.
      - pose proof (Tim _ _ _ H H0) as (?&?& H2).
        rewrite common_suffix_comm, <- H2.
        eapply IHlck; eauto.
        destruct Hin as [|[]]; auto; subst; exfalso;
          eapply clock_parent_not_refl; eauto.
    Qed.

  End Clock_operations.

  Ltac simpl_Foralls :=
    repeat
      match goal with
      | H: Forall _ [] |- _ => inv H
      | H: Forall _ [_] |- _ => inv H
      | H: Forall _ (_::_) |- _ => inv H
      | H: Forall2 _ [_] _ |- _ => inv H
      | H: Forall2 _ [] _ |- _ => inv H
      | H: Forall2 _ _ [_] |- _ => inv H
      | H: Forall2 _ _ [] |- _ => inv H
      end.

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
