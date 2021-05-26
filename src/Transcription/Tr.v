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

Module Type TR
       (Import Ids  : IDS)
       (Import Op   : OPERATORS)
       (Import OpAux: OPERATORS_AUX Ids Op)
       (Import Cks  : CLOCKS Ids Op OpAux)
       (L           : LSYNTAX  Ids Op OpAux Cks)
       (Import CE   : CESYNTAX Ids Op OpAux Cks)
       (NL          : NLSYNTAX Ids Op OpAux Cks CE).

  (* We have to define mmap in a section to make the termination-checker happy *)
  Section mmap.
    Context {A B : Type}.
    Variable (f : A -> res B).

    Fixpoint mmap (l: list A) {struct l} : res (list B) :=
      match l with
      | nil => OK nil
      | hd :: tl => do hd' <- f hd; do tl' <- mmap tl; OK (hd' :: tl')
      end.

    Remark mmap_inversion:
      forall (l: list A) (l': list B),
        mmap l = OK l' ->
        Forall2 (fun x y => f x = OK y) l l'.
    Proof.
      induction l; simpl; intros.
      inversion_clear H. constructor.
      destruct (bind_inversion _ _ H) as [hd' [P Q]].
      destruct (bind_inversion _ _ Q) as [tl' [R S]].
      inversion_clear S.
      constructor. auto. auto.
    Qed.

    Remark mmap_length: forall l l',
        mmap l = OK l' ->
        length l' = length l.
    Proof.
      induction l; intros * Map; simpl in *; monadInv Map; auto.
      simpl. f_equal; auto.
    Qed.
  End mmap.

  (* And so we need to rewrite monadInv... *)

  Ltac monadInv1 H :=
    match type of H with
    | (mmap ?F ?L = OK ?M) =>
      generalize (mmap_inversion F L _ H); intro
    | _ => Errors.monadInv1 H
    end.

  Ltac monadInv H :=
    simpl in *;
    monadInv1 H ||
              match type of H with
              | (?F _ _ _ _ _ _ _ _ = OK _) =>
                ((progress simpl in H) || unfold F in H); monadInv1 H
              | (?F _ _ _ _ _ _ _ = OK _) =>
                ((progress simpl in H) || unfold F in H); monadInv1 H
              | (?F _ _ _ _ _ _ = OK _) =>
                ((progress simpl in H) || unfold F in H); monadInv1 H
              | (?F _ _ _ _ _ = OK _) =>
                ((progress simpl in H) || unfold F in H); monadInv1 H
              | (?F _ _ _ _ = OK _) =>
                ((progress simpl in H) || unfold F in H); monadInv1 H
              | (?F _ _ _ = OK _) =>
                ((progress simpl in H) || unfold F in H); monadInv1 H
              | (?F _ _ = OK _) =>
                ((progress simpl in H) || unfold F in H); monadInv1 H
              | (?F _ = OK _) =>
                ((progress simpl in H) || unfold F in H); monadInv1 H
              end.

  Fixpoint to_lexp (e : L.exp) : res CE.exp :=
    match e with
    | L.Econst c                 => OK (CE.Econst c)
    | L.Eenum k ty               => OK (CE.Eenum k ty)
    | L.Evar x (ty, ck)          => OK (CE.Evar x ty)
    | L.Eunop op e (ty, ck)      => do le <- to_lexp e;
                                    OK (CE.Eunop op le ty)
    | L.Ebinop op e1 e2 (ty, ck) => do le1 <- to_lexp e1;
                                    do le2 <- to_lexp e2;
                                    OK (CE.Ebinop op le1 le2 ty)
    | L.Ewhen [e] x b ([ty], ck) => do le <- to_lexp e;
                                    OK (CE.Ewhen le x b)
    | L.Efby _ _ _ _
    | L.Earrow _ _ _ _
    | L.Ewhen _ _ _ _
    | L.Emerge _ _ _
    | L.Ecase _ _ _ _
    | L.Eapp _ _ _ _    => Error (msg "expression not normalized")
    end.

  (* Definition init_type ty := *)
  (*   match ty with *)
  (*   | Tprimitive cty => Econst (init_ctype cty) *)
  (*   | Tenum tn => Eenum 0 (Tenum tn) *)
  (*   end. *)

  (* Fixpoint add_whens (e : CE.exp) (ty : type) (ck : clock) := *)
  (*   match ck with *)
  (*   | Cbase => e *)
  (*   | Con ck' ckid (_, b) => CE.Ewhen (add_whens e ty ck') ckid b *)
  (*   end. *)

  Fixpoint to_cexp (e : L.exp) : res CE.cexp :=
    match e with
    | L.Econst _
    | L.Eenum _ _
    | L.Evar _ _
    | L.Eunop _ _ _
    | L.Ebinop _ _ _ _
    | L.Ewhen _ _ _ _                 => do le <- to_lexp e;
                                         OK (CE.Eexp le)

    | L.Emerge x es ([ty], ck) =>
      do ces <- mmap (fun es => match es with
                            | [e] => to_cexp e
                            | _ => Error (msg "control expression not normalized")
                            end) es;
      OK (CE.Emerge x ces ty)

    | L.Ecase e es [d] ([ty], (ck, _)) =>
      do le <- to_lexp e;
      do ces <- mmap (fun es => match es with
                            | Some [e] => do e' <- to_cexp e; OK (Some e')
                            | None => OK None
                            | _ => Error (msg "control expression not normalized")
                            end) es;
      do d' <- to_cexp d;
      OK (CE.Ecase le ces d')

    | L.Emerge _ _ _
    | L.Ecase _ _ _ _
    | L.Efby _ _ _ _
    | L.Earrow _ _ _ _
    | L.Eapp _ _ _ _    => Error (msg "control expression not normalized")
    end.

  Fixpoint suffix_of_clock (ck : clock) (acc : list (ident * (type * enumtag))) : list (ident * (type * enumtag)) :=
    match ck with
    | Cbase => acc
    | Con ck' x b => suffix_of_clock ck' ((x, b) :: acc)
    end.

  Fixpoint clock_of_suffix (sfx : list (ident * (type * enumtag))) (ck : clock) : clock :=
    match sfx with
    | [] => ck
    | (x, b) :: sfx' => clock_of_suffix sfx' (Con ck x b)
    end.

  Fixpoint common_suffix (sfx1 sfx2 : list (ident * (type * enumtag))) : list (ident * (type * enumtag)) :=
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
    | L.Econst c => OK (Const c)
    | L.Eenum k _ => OK (Enum k)
    | L.Ewhen [e] _ _ _ => to_constant e
    | _ => Error (msg "not a constant")
    end.

  Definition vars_of (es : list L.exp) :=
    omap (fun e => match e with
                | L.Evar x (_, (ck, _)) => Some (x, ck)
                | _ => None
                end) es.

  Definition to_equation (env : Env.t (type * clock)) (envo : ident -> res unit)
                         (eq : L.equation) : res NL.equation :=
    let (xs, es) := eq in
    match es with
    | [e] =>
      match e with
      | L.Eapp f es r _ =>
        do les <- mmap to_lexp es;
        match (vars_of r) with
        | Some xr => OK (NL.EqApp xs (find_base_clock (L.clocksof es)) f les xr)
        | _ => Error (msg "reset equation not normalized")
        end
      | L.Efby [e0] [e] r _ =>
        match xs with
        | [x] =>
          do _  <- envo x;
          do c0 <- to_constant e0;
          do ck <- find_clock env x;
          do le <- to_lexp e;
          match (vars_of r) with
          | Some xr => OK (NL.EqFby x ck c0 le xr)
          | _ => Error (msg "fby equation not normalized")
          end
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

  Lemma find_clock_in_env :
    forall x env ty ck,
      Env.find x env = Some (ty, ck) ->
      find_clock env x = OK ck.
  Proof.
    intros * H. unfold find_clock. now rewrite H.
  Qed.

  Lemma find_clock_out {prefs} : forall (n : @L.node prefs) x ty ck,
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

  Definition mmap_to_equation {prefs} env envo (n : @L.node prefs) :
    res { neqs | mmap (to_equation env envo) n.(L.n_eqs) = OK neqs }.
  Proof.
    destruct (mmap (to_equation env envo) n.(L.n_eqs)).
    left. eauto.
    right. auto.
  Defined.

  Unset Program Cases.
  Program Definition to_node (n : @L.node norm2_prefs) : res NL.node :=
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
    monadInv1 P.
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

    monadInv Heqr. induction H as [| eq eq' leq leq' Htoeq ].
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
      + apply IHForall2; auto.
    - apply IHForall2; eauto.
  Qed.

  Next Obligation.
    specialize (L.n_nodup n) as Hndup.
    repeat rewrite app_assoc in *. apply NoDupMembers_app_l in Hndup; auto.
  Qed.

  (* NL.n_good obligation *)
  Next Obligation.
    pose proof (L.n_good n) as (Hgood&Hat).
    split; auto.
    repeat rewrite map_app in *.
    eapply Forall_impl; [|eapply Forall_incl; eauto].
    - intros * [?|(pref&?&?&?)]; subst; [left|right]; auto.
      exists pref. eauto.
      unfold norm2_prefs, norm1_prefs, elab_prefs in H1.
      repeat rewrite PSF.add_iff in *. rewrite PS.singleton_spec in *.
      destruct H1 as [?|[?|?]]; subst; split; eauto.
    - apply incl_appr', incl_appr', incl_appl, incl_refl.
  Qed.

  Definition to_global (G : L.global) :=
    do nds' <- mmap to_node G.(L.nodes);
    OK (NL.Global G.(L.enums) nds').

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

  Lemma find_node_In {prefs} : forall f (G: @L.global prefs) n,
      L.find_node f G = Some n -> In n G.(L.nodes).
  Proof.
    intros * Hfind. unfold L.find_node in Hfind.
    apply option_map_inv in Hfind as ((?&?)&Hfind&?); subst.
    eapply CommonProgram.find_unit_In in Hfind as (?&?); auto.
  Qed.

  Lemma to_node_name n n' :
    to_node n = OK n' -> L.n_name n = NL.n_name n'.
  Proof.
    intros * Htr. tonodeInv Htr. now simpl.
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
    destruct G as (?&nds). unfold to_global.
    revert P.
    induction nds; intros * Htrans Hfind. inversion Hfind.
    apply L.find_node_cons in Hfind.
    destruct Hfind as [(Heq&?)|(Hneq&Hfind)]; subst.
    - monadInv Htrans. simpl in EQ. monadInv EQ.
      exists x0. split; eauto.
      simpl. apply to_node_name in EQ0.
      rewrite NL.find_node_now; eauto.
    - monadInv Htrans. simpl in *. monadInv EQ.
      eapply IHnds in Hfind as (n'&P'&nP). 2:rewrite EQ; simpl; eauto.
      exists n'. split; eauto.
      rewrite NL.find_node_other; eauto.
      apply to_node_name in EQ0. rewrite <-EQ0; auto.
  Qed.

  Lemma find_node_global' (G: L.global) (P: NL.global) (f: ident) (n': NL.node) :
    to_global G = OK P ->
    NL.find_node f P = Some n' ->
    exists n, L.find_node f G = Some n /\ to_node n = OK n'.
  Proof.
    destruct G as (?&nds). unfold to_global.
    revert P.
    induction nds; intros * Htrans Hfind; simpl in *; monadInv Htrans; simpl in *; try solve [inversion Hfind].
    monadInv EQ.
    destruct (ident_eq_dec (NL.n_name x0) f) eqn:Hname.
    - clear EQ.
      erewrite L.find_node_now. 2:erewrite to_node_name; eauto.
      erewrite NL.find_node_now in Hfind; eauto. inv Hfind; eauto.
    - erewrite NL.find_node_other in Hfind; eauto.
      eapply IHnds in Hfind as (?&Hfind'&Hton); eauto. 2:rewrite EQ; eauto.
      eexists; split; eauto.
      rewrite L.find_node_other; eauto.
      erewrite to_node_name; eauto.
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

    Lemma envs_eq_find' :
      forall env cenv x ck,
        envs_eq env cenv ->
        find_clock env x = OK ck ->
        In (x, ck) cenv.
    Proof.
      unfold find_clock, envs_eq. intros * Heq Hfind.
      rewrite Heq.
      destruct Env.find.
      - destruct p. inv Hfind. eexists; eauto.
      - inv Hfind.
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
        apply Env.find_env_from_list' in Hfind.
        destruct Hfind as [Hin | [Hin Hfind]];
          rewrite idck_app; apply in_app_iff.
        left. rewrite In_idck_exists. eauto.
        right. unfold envs_eq in Heq. rewrite Heq. eauto.
    Qed.

    Lemma envs_eq_node {prefs} (n : @L.node prefs) :
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
      now rewrite <-(app_nil_l [(i, p)]),
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
      - apply andb_prop in EQ as [H H1].
        apply Peqb_true_eq in H. rewrite equiv_decb_equiv in H1. inv H1.
        Coq.Bool.Bool.destr_bool; f_equal; auto; f_equal.
      - apply andb_prop in EQ as [H].
        apply Peqb_true_eq in H. rewrite equiv_decb_equiv in H0. inv H0.
        apply Bool.andb_false_iff in EQ0 as [];
          Coq.Bool.Bool.destr_bool.
        now rewrite Pos.eqb_refl in H.
        now rewrite equiv_decb_refl in H.
      - apply andb_prop in EQ0 as [H].
        apply Peqb_true_eq in H. rewrite equiv_decb_equiv in H0. inv H0.
        apply Bool.andb_false_iff in EQ as [];
          Coq.Bool.Bool.destr_bool.
        now rewrite Pos.eqb_refl in H.
        now rewrite equiv_decb_refl in H.
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

  Fact to_global_names : forall name G G',
      Forall (fun n => (name <> L.n_name n)%type) G.(L.nodes) ->
      to_global G = OK G' ->
      Forall (fun n => (name <> NL.n_name n)%type) G'.(NL.nodes).
  Proof.
    unfold to_global.
    intros ? (enms&nds).
    induction nds; intros * Hnames Htog; inv Hnames; monadInv Htog; simpl; auto.
    monadInv EQ. constructor; auto.
    - erewrite to_node_name in H1; eauto.
    - eapply IHnds in H2; eauto. 2:rewrite EQ; simpl; eauto.
      simpl in H2; auto.
  Qed.

  Fact to_global_enums : forall G G',
      to_global G = OK G' ->
      NL.enums G' = L.enums G.
  Proof.
    intros (?&?) * Htog.
    monadInv Htog; auto.
  Qed.

  Fact vars_of_spec: forall es xr,
      vars_of es = Some xr <->
      Forall2 (fun e '(x, ck) => exists ty n, e = L.Evar x (ty, (ck, n))) es xr.
  Proof.
    induction es; intros *; simpl in *; split; intros H.
    - inv H; auto.
    - inv H; auto.
    - destruct a; inv H.
      destruct a as (?&?&?). cases; inv H1.
      constructor; eauto. eapply IHes; eauto.
    - inv H. destruct y, H2 as (?&?&?); subst.
      eapply IHes in H4. rewrite H4; auto.
  Qed.

  Lemma vars_of_Some: forall es,
      Forall (fun e => exists x ann, e = L.Evar x ann) es ->
      exists xr, vars_of es = Some xr.
  Proof.
    induction es; intros F; inv F.
    - exists []; auto.
    - eapply IHes in H2 as (xr&?).
      destruct H1 as (?&(?&?&?)&?); subst.
      simpl. setoid_rewrite H. eauto.
  Qed.

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

End TR.

Module TrFun
       (Ids   : IDS)
       (Op    : OPERATORS)
       (OpAux : OPERATORS_AUX Ids Op)
       (Cks   : CLOCKS   Ids Op OpAux)
       (L     : LSYNTAX  Ids Op OpAux Cks)
       (CE    : CESYNTAX Ids Op OpAux Cks)
       (NL    : NLSYNTAX Ids Op OpAux Cks CE)
       <: TR Ids Op OpAux Cks L CE NL.
  Include TR Ids Op OpAux Cks L CE NL.
End TrFun.
