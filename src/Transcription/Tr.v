From Velus Require Import Common.
From Velus Require Import Environment.
From Velus Require Import Operators.
From Velus Require Import Clocks.
From Velus Require Import Lustre.StaticEnv.
From Velus Require Import Lustre.LSyntax.
From Velus Require Import CoreExpr.CESyntax.
From Velus Require Import NLustre.NLSyntax.

From Coq Require Import Permutation.
From Coq Require Import String.
From Coq Require Import Sorting.Mergesort.

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
       (Senv        : STATICENV Ids Op OpAux Cks)
       (L           : LSYNTAX  Ids Op OpAux Cks Senv)
       (Import CE   : CESYNTAX Ids Op OpAux Cks)
       (NL          : NLSYNTAX Ids Op OpAux Cks CE).

  Fixpoint to_lexp (e : L.exp) : res CE.exp :=
    match e with
    | L.Econst c                 => OK (CE.Econst c)
    | L.Eenum k ty               => OK (CE.Eenum k ty)
    | L.Evar x (ty, ck)          => OK (CE.Evar x ty)
    | L.Elast x (ty, ck)         => OK (CE.Elast x ty)
    | L.Eunop op e (ty, ck)      => do le <- to_lexp e;
                                    OK (CE.Eunop op le ty)
    | L.Ebinop op e1 e2 (ty, ck) => do le1 <- to_lexp e1;
                                    do le2 <- to_lexp e2;
                                    OK (CE.Ebinop op le1 le2 ty)
    | L.Ewhen [e] x b ([ty], ck) => do le <- to_lexp e;
                                   OK (CE.Ewhen le x b)
    | L.Eextcall _ _ _
    | L.Efby _ _ _
    | L.Earrow _ _ _
    | L.Ewhen _ _ _ _
    | L.Emerge _ _ _
    | L.Ecase _ _ _ _
    | L.Eapp _ _ _ _    => Error (msg "expression not normalized")
    end.

  (** In NLustre, `case` and `merge` branches have to be sorted in constructor order.
      That is not the case in Lustre.
      We sort the branches during Transcription
   *)
  Module BranchesOrder <: Orders.TotalLeBool'.

    Definition t : Type := (enumtag * cexp).

    Definition leb (s1 s2 : t) : bool := ((fst s1) <=? (fst s2)).

    Lemma leb_total:
      forall s1 s2,
        leb s1 s2 = true \/ leb s2 s1 = true.
    Proof.
      destruct s1 as (n1 & a1), s2 as (n2 & a2).
      unfold leb; simpl.
      setoid_rewrite OrdersEx.Nat_as_OT.leb_compare.
      destruct (n1 ?= n2) eqn:Hn; auto.
      apply Nat.compare_gt_iff in Hn.
      apply Nat.compare_lt_iff in Hn.
      rewrite Hn; auto.
    Qed.

  End BranchesOrder.
  Module BranchesSort := Sort BranchesOrder.

  (** For total `case` (without a default branch) we need to add a well-typed and well-clocked default branch.
      The branch will never be read, so we don't care about it's semantics. *)
  Definition init_type (ty : type) :=
    match ty with
    | Tprimitive cty => Econst (Op.init_ctype cty)
    | Tenum _ _ => Eenum 0 ty
    end.

  Fixpoint add_whens (e: CE.exp) (ty: type) (ck: clock) : CE.exp :=
    match ck with
    | Cbase => e
    | Con ck' x (tx, k) => Ewhen (add_whens e ty ck') (x, tx) k
    end.

  (** For partial `case`, we add the missing branches *)
  Fixpoint complete_branches (s : list enumtag) (brs : list (enumtag * cexp)) : list (enumtag * option cexp) :=
    match s with
    | [] => map (fun '(i, e) => (i, Some e)) brs
    | k::s =>
      match brs with
      | [] => (k, None)::(complete_branches s brs)
      | (tag, e)::tl => if (tag =? k) then (tag, Some e)::(complete_branches s tl)
                      else (k, None)::(complete_branches s brs)
      end
    end.

  Fixpoint to_cexp (e : L.exp) : res CE.cexp :=
    match e with
    | L.Econst _
    | L.Eenum _ _
    | L.Evar _ _
    | L.Elast _ _
    | L.Eunop _ _ _
    | L.Ebinop _ _ _ _
    | L.Ewhen _ _ _ _                 => do le <- to_lexp e;
                                         OK (CE.Eexp le)

    | L.Emerge x es ([ty], ck) =>
      do ces <- mmap (fun '(i, es) => match es with
                            | [e] => do ce <- to_cexp e; OK (i, ce)
                            | _ => Error (msg "control expression not normalized")
                            end) es;
      let ces := BranchesSort.sort ces in
      OK (CE.Emerge x (map snd ces) ty)

    | L.Ecase e es None ([ty], ck) =>
      do le <- to_lexp e;
      do ces <- mmap (fun '(i, es) => match es with
                            | [e] => do ce <- to_cexp e; OK (i, ce)
                            | _ => Error (msg "control expression not normalized")
                            end) es;
      let ces := map (fun '(i, es) => Some es) (BranchesSort.sort ces) in
      OK (CE.Ecase le ces (Eexp (add_whens (init_type ty) ty ck)))
    | L.Ecase e es (Some [d]) ([_], ck) =>
      do le <- to_lexp e;
      do ces <- mmap (fun '(i, es) => match es with
                            | [e] => do ce <- to_cexp e; OK (i, ce)
                            | _ => Error (msg "control expression not normalized")
                            end) es;
      do d' <- to_cexp d;
      let ty := L.typeof e in
      match ty with
      | [Tenum _ tn] =>
        let ces := (complete_branches (seq 0 (length tn)) (BranchesSort.sort ces)) in
        OK (CE.Ecase le (map snd ces) d')
      | _ => Error (msg "type error : expected enumerated type for condition")
      end

    | L.Eextcall _ _ _
    | L.Emerge _ _ _
    | L.Ecase _ _ _ _
    | L.Efby _ _ _
    | L.Earrow _ _ _
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

  (* Definition find_clock (env : Env.t (type * clock)) (x : ident) : res clock := *)
  (*   match Env.find x env with *)
  (*   | None => Error (msg "find_clock failed unexpectedly") *)
  (*   | Some (ty, ck) => OK ck *)
  (*   end. *)

  Definition find_clock (env : Env.t clock) (x : ident) : res clock :=
    match Env.find x env with
    | None => Error (msg "find_clock failed unexpectedly")
    | Some ck => OK ck
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
                | L.Evar x (_, ck) => Some (x, ck)
                | _ => None
                end) es.

  Definition to_equation (env : Env.t clock) (envo : ident -> res unit)
                         (xr : list (ident * clock)) (eq : L.equation) : res NL.equation :=
    let (xs, es) := eq in
    match es with
    | [e] =>
      match e with
      | L.Eapp f es r _ =>
        do les <- mmap to_lexp es;
        match (vars_of r) with
        | Some xr' => OK (NL.EqApp xs (find_base_clock (L.clocksof es)) f les (xr++xr'))
        | _ => Error (msg "reset equation not normalized")
        end
      | L.Efby [e0] [e] _ =>
        match xs with
        | [x] =>
          do _  <- envo x;
          do c0 <- to_constant e0;
          do ck <- find_clock env x;
          do le <- to_lexp e;
          OK (NL.EqFby x ck c0 le xr)
        | _ => Error (msg "fby equation not normalized")
        end
      | L.Eextcall f es (tyout, ck) =>
          match xs with
          | [x] =>
              do les <- mmap to_lexp es;
              OK (NL.EqDef x ck (Eextcall f les tyout))
          | _ => Error (msg "equation not normalized")
          end
      | _ =>
        match xs with
        | [x] =>
          do ck <- find_clock env x;
          do ce <- to_cexp e;
          OK (NL.EqDef x ck (Ecexp ce))
        | _ => Error (msg "basic equation not normalized")
        end
      end
    | _ => Error (msg "equation not normalized")
    end.

  Fixpoint block_to_equation (env : Env.t clock) (envo : ident -> res unit)
           (xr : list (ident * clock)) (d : L.block) : res NL.equation :=
    match d with
    | L.Beq eq =>
      to_equation env envo xr eq
    | L.Blast x e =>
        let ty := List.hd (OpAux.bool_velus_type) (L.typeof e) in
        do ck <- find_clock env x;
        do c <- to_constant e;
        OK (NL.EqLast x ty ck c xr)
    | L.Breset [block] (L.Evar x (_, ck)) =>
      block_to_equation env envo ((x, ck)::xr) block
    | _ => Error (msg "block not normalized")
    end.

  Lemma find_clock_in_env :
    forall x env ck,
      Env.find x env = Some ck ->
      find_clock env x = OK ck.
  Proof.
    intros * H. unfold find_clock. now rewrite H.
  Qed.

  (* Lemma find_clock_out {PSyn prefs} : forall (n : @L.node PSyn prefs) x ty ck, *)
  (*     In (x, (ty, ck)) (map (fun '(x, (ty, ck, _, _)) => (x, (ty, ck))) (L.n_out n)) -> *)
  (*     find_clock (Env.adds' (idfst (L.n_in n)) (Env.from_list (map (fun '(x, (ty, ck, _, _)) => (x, (ty, ck))) (L.n_out n)))) x = OK ck. *)
  (* Proof. *)
  (*   intros * Hin. *)
  (*   unfold Env.from_list. eapply find_clock_in_env. *)
  (*   apply In_InMembers in Hin as Hinm. *)
  (*   pose proof (L.n_nodup n) as (Hnodup&_). *)
  (*   rewrite Env.gsso'. apply Env.In_find_adds'; eauto. *)
  (*   - erewrite fst_NoDupMembers, map_map, map_ext; eauto using NoDup_app_r. intros; destruct_conjs; auto. *)
  (*   - rewrite InMembers_idfst, fst_InMembers. intros ?. eapply NoDup_app_In; eauto. *)
  (*     solve_In. *)
  (* Qed. *)

  Lemma to_eq_vars_defined eq eq' :
    forall env envo xr,
      to_equation env envo xr eq = OK eq' -> NL.var_defined eq' = fst eq.
  Proof.
    intros * Htoeq.
    unfold to_equation in Htoeq.
    cases; monadInv Htoeq; inv EQ; simpl; auto.
  Qed.

  Lemma to_eq_lasts_defined eq eq' :
    forall env envo xr,
      to_equation env envo xr eq = OK eq' -> NL.last_defined eq' = [].
  Proof.
    intros * Htoeq.
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

  Definition mmap_block_to_equation {PSyn prefs} env envo (n: @L.node PSyn prefs) :
    res { neqs | match n.(L.n_block) with
                 | L.Blocal (L.Scope locs blks) =>
                   do neqs <- mmap (block_to_equation (Env.adds' (idsnd (idfst (idfst locs))) env) envo []) blks;
                   OK (locs, neqs)
                 | _ => Error (msg "node not normalized")
                 end = OK neqs }.
  Proof.
    destruct (L.n_block n); simpl.
    1-5:right; exact (msg "node not normalized").
    destruct s as [? l0].
    destruct (mmap (block_to_equation (Env.adds' (idsnd (idfst (idfst l))) env) envo []) l0).
    left. simpl. eauto.
    right. auto.
  Defined.

  Remark mlength_map:
    forall {A B : Type} (f: A -> res B) l l',
      mmap f l = OK l' ->
      length l' = length l.
  Proof.
    induction l; simpl; intros * Hmap; monadInv Hmap; simpl; auto.
  Qed.

  Unset Program Cases.
  Program Definition to_node (n : @L.node L.normalized fby_prefs) : res NL.node :=
    let ins := idfst n.(L.n_in) in
    let outs := idfst (idfst n.(L.n_out)) in
    let envo := Env.from_list (idsnd outs) in
    let env := Env.adds' (idsnd ins) envo in
    let is_not_out :=
        fun x => if Env.mem x envo
              then Error (msg "output variable defined as a fby")
              else OK tt in
    match mmap_block_to_equation env is_not_out n with
    | OK (exist _ res P) =>
      OK {|
          NL.n_name     := n.(L.n_name);
          NL.n_in       := ins;
          NL.n_out      := outs;
          NL.n_vars     := map (fun xtc => (fst xtc, (fst (fst (fst (snd xtc))), snd (fst (fst (snd xtc))), isSome (snd (snd xtc))))) (fst res);
          NL.n_eqs      := snd res;

          NL.n_ingt0    := L.n_ingt0 n;
          NL.n_outgt0   := L.n_outgt0 n;
          NL.n_defd     := _;
          NL.n_vout     := _;
          NL.n_nodup    := _;
          NL.n_good     := _
        |}
    | Error e => Error e
    end.

  Next Obligation. now rewrite length_idfst. Qed.
  Next Obligation. now rewrite 2 length_idfst. Qed.
  (* NL.n_defd obligation *)
  Next Obligation.
    rewrite map_map, ? map_fst_idfst; simpl.
    clear H. rename l into vars. rename l0 into neqs.
    pose proof (L.n_nodup n) as (_&Hnd).
    pose proof (L.n_syn n) as Hsyn. inversion Hsyn as [??? _ Syn2 (vd&Hvars&Hperm)]; subst; clear Hsyn; rewrite <-H0 in *.
    monadInv1 P. inv Hvars. inv H1. destruct H4 as (xs0&Hvd&Hperm').
    assert (NL.vars_defined neqs = concat xs0).
    { revert neqs EQ. clear - Syn2 Hvd. induction Hvd; inv Syn2; simpl.
      - intros neqs Htr. inv Htr. auto.
      - intros neqs Htoeq. monadInv Htoeq.
        apply IHHvd in EQ1; auto. simpl.
        f_equal; auto.
        clear - H H2 EQ.
        revert EQ y H. generalize (@nil (ident * clock)) as xr.
        induction x using L.block_ind2; intros * EQ ? Hvd; simpl in *; inv H2; inv Hvd; try congruence.
        + apply to_eq_vars_defined in EQ; auto.
        + monadInv EQ. reflexivity.
        + cases; simpl.
          simpl_Forall. rewrite app_nil_r.
          eapply H3; eauto.
    }
    rewrite H, Hperm', Hperm, Permutation_app_comm. reflexivity.
  Qed.

  (* NL.n_lastd obligation *)
  Next Obligation.
    clear H. rename l into vars. rename l0 into neqs.
    pose proof (L.n_nodup n) as (_&Hnd).
    pose proof (L.n_lastd n) as (?&Last&Perm).
    pose proof (L.n_syn n) as Hsyn. inversion Hsyn as [??? Syn1 Syn2 (vd&Hvars&Hperm)]; subst; clear Hsyn; rewrite <-H0 in *.
    monadInv1 P. inv Last. inv H1. destruct H4 as (xs0&Hvd&Hperm').
    assert (NL.lasts_defined neqs = concat xs0).
    { revert neqs EQ. clear - Syn2 Hvd. induction Hvd; inv Syn2; simpl.
      - intros neqs Htr. inv Htr. auto.
      - intros neqs Htoeq. monadInv Htoeq.
        apply IHHvd in EQ1; auto. simpl.
        f_equal; auto.
        clear - H H2 EQ.
        revert EQ y H. generalize (@nil (ident * clock)) as xr.
        induction x using L.block_ind2; intros * EQ ? Hvd; simpl in *; inv H2; inv Hvd; try congruence.
        + apply to_eq_lasts_defined in EQ; auto.
        + monadInv EQ. reflexivity.
        + cases; simpl.
          simpl_Forall. rewrite app_nil_r.
          eapply H3; eauto.
    }
    simpl. rewrite H, Hperm', Perm, Permutation_app_comm.
    unfold L.lasts_of_decls. rewrite map_filter_nil with (xs:=L.n_out n), app_nil_r.
    2:{ simpl_Forall. unfold L.decl in *. destruct_conjs. subst; auto. }
    clear - vars. induction vars as [|(?&((?&?)&?)&[])]; simpl; auto.
  Qed.

  Next Obligation.
    simpl_In. destruct o; simpl in *; [|congruence].
    assert (In x (NL.vars_defined l0)) as In1.
    { pose proof (to_node_obligation_3 n) as Def. simpl in *.
      rewrite P in Def.
      assert ({neqs : list L.decl * list NL.equation | OK (l, l0) = OK neqs}) as I.
      { econstructor. reflexivity. }
      specialize (Def I _ eq_refl). simpl in *. clear I.
      rewrite Def. apply in_app_iff. left. solve_In. }
    pose proof (L.n_syn n) as Hsyn. inversion Hsyn as [??? _ Syn2 (vd&Hvars&Hperm)]; subst; clear Hsyn; rewrite <-H1 in *.
    rewrite <-NL.is_filtered_vars_defined, NL.def_cexp_rhs in In1.
    monadInv P. apply mmap_inversion in EQ.
    rewrite ? in_app_iff in In1. destruct In1 as [[In1|In1]|[In1|In1]]; auto.
    all:exfalso.
    - clear - Syn2 In1 Hin EQ.
      induction EQ; inv Syn2; simpl in *. inv In1.
      cases_eqn Eq; simpl in *; auto. apply in_app_iff in In1 as [In1|In1]; auto.
      clear IHEQ EQ. revert b1 H Eq In1. generalize (@nil (ident * clock)) as xrs.
      take (L.normalized_block _ _ _) and induction it; intros; simpl in *.
      + inv H; simpl in *; try monadInv H0.
        * cases; try monadInv EQ0; simpl in *; try congruence.
        * simpl in *. congruence.
        * cases. monadInv H0. simpl in *. destruct In1 as [In1|In1]; inv In1.
          eapply H2. unfold L.lasts_of_decls. solve_In.
        * cases; monadInv H0; simpl in *; try congruence.
          inv H1. inv H.
      + monadInv H0. simpl in *. inv In1.
      + destruct ann. eapply IHit in H; eauto.
    - clear - Syn2 In1 Hin EQ.
      induction EQ; inv Syn2; simpl in *. inv In1.
      cases_eqn Eq; simpl in *; auto. apply in_app_iff in In1 as [In1|In1]; auto.
      clear IHEQ EQ. revert b1 H Eq In1. generalize (@nil (ident * clock)) as xrs.
      take (L.normalized_block _ _ _) and induction it; intros; simpl in *.
      + inv H; simpl in *; try monadInv H0.
        * cases; try monadInv EQ0; simpl in *.
          simpl_Forall. eapply H4. unfold L.lasts_of_decls. solve_In.
        * simpl in *. congruence.
        * cases. monadInv H0. simpl in *. congruence.
        * cases; monadInv H0; simpl in *; try congruence.
          inv H1. inv H.
      + monadInv H0. simpl in *. inv In1.
      + destruct ann. eapply IHit in H; eauto.
    - clear - Syn2 In1 Hin EQ.
      induction EQ; inv Syn2; simpl in *. inv In1.
      cases_eqn Eq; simpl in *; auto. apply in_app_iff in In1 as [In1|In1]; auto.
      clear IHEQ EQ. revert b1 H Eq In1. generalize (@nil (ident * clock)) as xrs.
      take (L.normalized_block _ _ _) and induction it; intros; simpl in *.
      + inv H; simpl in *; try monadInv H0.
        * cases; try monadInv EQ0; simpl in *; congruence.
        * simpl in *. destruct In1 as [In1|In1]; inv In1.
          apply H5. unfold L.lasts_of_decls. solve_In.
        * cases. monadInv H0. simpl in *. congruence.
        * cases; monadInv H0; simpl in *; try congruence.
          inv H1. inv H.
      + monadInv H0. simpl in *. inv In1.
      + destruct ann. eapply IHit in H; eauto.
  Qed.

  (* NL.n_vout obligation *)
  Next Obligation.
    clear H0. rename H into Hin. rename l into vars. rename l0 into neqs.
    cases. rename l0 into blks.
    monadInv P.
    eapply mmap_inversion in EQ.
    induction EQ as [| eq eq' leq leq' Htoeq ].
    intro Hbad. inv Hbad.
    simpl. destruct (NL.is_fby leq) eqn:?; auto.
    unfold NL.vars_defined, flat_map. simpl. rewrite in_app.
    intro Hi. destruct Hi.
    - clear - Htoeq Heqb H Hin.
      revert Htoeq. generalize (@nil (ident * clock)).
      induction eq using L.block_ind2; intros; simpl in *; try congruence.
      + unfold to_equation in Htoeq. destruct eq.
        cases_eqn E; monadInv1 Htoeq; inv Heqb.
        simpl in H. destruct H; auto. subst. inv EQ.
        apply Env.Props.P.F.not_mem_in_iff in E8. apply E8.
        simpl_In.
        eapply Env.find_In. eapply Env.In_find_adds'; simpl; eauto.
        2:{ solve_In. }
        destruct n. simpl. pose proof n_nodup as (Hnodup&_).
        rewrite NoDupMembers_idsnd, ? NoDupMembers_idfst, fst_NoDupMembers; eauto using NoDup_app_r.
      + monadInv Htoeq. simpl in *. congruence.
      + cases. apply Forall_singl in H0.
        eapply H0; eauto.
    - eapply IHEQ; eauto.
  Qed.

  Next Obligation.
    clear H. rename l into vars.
    pose proof (L.n_nodup n) as (Hndup1&Hndup2).
    cases. rename l3 into blks. monadInv P.
    inv Hndup2. repeat L.inv_scope.
    rewrite ? map_fst_idfst, map_map. simpl.
    rewrite (Permutation_app_comm (map _ vars)), app_assoc.
    apply NoDup_app'; eauto.
    - now apply fst_NoDupMembers.
    - simpl_Forall. intros In. apply fst_InMembers in In. eapply H5; eauto.
  Qed.

  (* NL.n_good obligation *)
  Next Obligation.
    clear H. rename l into vars.
    pose proof (L.n_good n) as (Hgood1&Hgood2&Hat).
    split; auto.
    cases. monadInv P.
    rewrite ? map_fst_idfst, map_map. simpl.
    rewrite (Permutation_app_comm (map _ vars)), app_assoc.
    inv Hgood2. L.inv_scope.
    apply Forall_app; split; simpl_Forall.
    1,2:(take (AtomOrGensym _ _) and inversion_clear it as [?|(pref&Hpref&?&?&?)];
         subst; [left|right]; auto;
         exists pref; eauto;
         unfold fby_prefs, last_prefs, norm1_prefs, local_prefs, switch_prefs, auto_prefs, elab_prefs in Hpref;
         repeat rewrite PSF.add_iff in *; rewrite PS.singleton_spec in *;
         repeat (take (_ \/ _) and destruct it; eauto 11)).
  Qed.

  Definition to_global (G : L.global) :=
    do nds' <- mmap to_node G.(L.nodes);
    OK (NL.Global G.(L.types) G.(L.externs) nds').

  Ltac tonodeInv H :=
    match type of H with
    | (to_node ?n = OK _) =>
      let Hs := fresh in
      let Hmmap := fresh "Hmmap" in
      unfold to_node in H;
      destruct(mmap_block_to_equation
                 (Env.adds' (idsnd (idfst (L.n_in n)))
                            (Env.from_list (idsnd (idfst (idfst n.(L.n_out))))))
            (fun x : Env.key =>
             if Env.mem x (Env.from_list (idsnd (idfst (idfst n.(L.n_out)))))
             then Error (msg "output variable defined as a fby")
             else OK tt) n)
      as [ Hs | Hs ];
      try (destruct Hs as ((?&?) & Hmmap)); inv H
    end.

  Lemma find_node_In {PSyn prefs} : forall f (G: @L.global PSyn prefs) n,
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
    to_node n = OK n' -> idfst (L.n_in n) = NL.n_in n'.
  Proof.
    intro Htr. tonodeInv Htr. now simpl.
  Qed.

  Lemma to_node_out n n' :
    to_node n = OK n' -> idfst (idfst (L.n_out n)) = NL.n_out n'.
  Proof.
    intro Htr. tonodeInv Htr. now simpl.
  Qed.

  (* Lemma to_node_vars n n' : *)
  (*   to_node n = OK n' -> L.n_vars n = NL.n_vars n'. *)
  (* Proof. *)
  (*   intro Htr. tonodeInv Htr. now simpl. *)
  (* Qed. *)

  Lemma find_node_global (G: L.global) (P: NL.global) (f: ident) (n: L.node) :
    to_global G = OK P ->
    L.find_node f G = Some n ->
    exists n', NL.find_node f P = Some n' /\ to_node n = OK n'.
  Proof.
    destruct G. unfold to_global.
    revert P.
    induction nodes; intros * Htrans Hfind. inversion Hfind.
    apply L.find_node_cons in Hfind.
    destruct Hfind as [(Heq&?)|(Hneq&Hfind)]; subst.
    - monadInv Htrans. simpl in EQ. monadInv EQ.
      exists x0. split; eauto.
      simpl. apply to_node_name in EQ0.
      rewrite NL.find_node_now; eauto.
    - monadInv Htrans. simpl in *. monadInv EQ.
      eapply IHnodes in Hfind as (n'&P'&nP). 2:rewrite EQ; simpl; eauto.
      exists n'. split; eauto.
      rewrite NL.find_node_other; eauto.
      apply to_node_name in EQ0. rewrite <-EQ0; auto.
  Qed.

  Lemma find_node_global' (G: L.global) (P: NL.global) (f: ident) (n': NL.node) :
    to_global G = OK P ->
    NL.find_node f P = Some n' ->
    exists n, L.find_node f G = Some n /\ to_node n = OK n'.
  Proof.
    destruct G. unfold to_global.
    revert P.
    induction nodes; intros * Htrans Hfind; simpl in *; monadInv Htrans; simpl in *; try solve [inversion Hfind].
    monadInv EQ.
    destruct (ident_eq_dec (NL.n_name x0) f) eqn:Hname.
    - clear EQ.
      erewrite L.find_node_now. 2:erewrite to_node_name; eauto.
      erewrite NL.find_node_now in Hfind; eauto. inv Hfind; eauto.
    - erewrite NL.find_node_other in Hfind; eauto.
      eapply IHnodes in Hfind as (?&Hfind'&Hton); eauto. 2:rewrite EQ; eauto.
      eexists; split; eauto.
      rewrite L.find_node_other; eauto.
      erewrite to_node_name; eauto.
  Qed.

  Section Envs_eq.

    Definition envs_eq (env : Env.t clock) (cenv : Senv.static_env) :=
      forall x ck,
        Senv.HasClock cenv x ck <-> Env.find x env = Some ck.

    Lemma envs_eq_find :
      forall env cenv x ck,
        envs_eq env cenv ->
        Senv.HasClock cenv x ck ->
        find_clock env x = OK ck.
    Proof.
      unfold find_clock, envs_eq. intros * Heq Hin.
      rewrite Heq in Hin. now rewrite Hin.
    Qed.

    Lemma envs_eq_find' :
      forall env cenv x ck,
        envs_eq env cenv ->
        find_clock env x = OK ck ->
        Senv.HasClock cenv x ck.
    Proof.
      unfold find_clock, envs_eq. intros * Heq Hfind.
      destruct Env.find as [|] eqn:Eq; inv Hfind; auto.
      apply Heq in Eq; eauto.
    Qed.

    Lemma envs_eq_app_comm :
      forall env (xs ys : Senv.static_env),
        envs_eq env (xs ++ ys)
        <-> envs_eq env (ys ++ xs).
    Proof.
      split; unfold envs_eq; intros Heq *.
      all:rewrite Permutation_app_comm; auto.
    Qed.

    Lemma env_eq_env_from_list:
      forall xs,
        NoDupMembers xs ->
        envs_eq (Env.from_list (Senv.idck xs)) xs.
    Proof.
      intros xs Hnodup x ck. split.
      - intro Hxs.
        apply Env.In_find_adds'; auto.
        1,2:unfold Senv.idck.
        + apply NoDupMembers_map; auto.
        + inv Hxs. solve_In.
      - intro Hfind.
        apply Env.from_list_find_In in Hfind; auto.
        simpl_In. econstructor; eauto.
    Qed.

    Lemma env_eq_env_adds':
      forall s xs ys,
        NoDupMembers (xs ++ ys) ->
        envs_eq s ys ->
        envs_eq (Env.adds' (Senv.idck xs) s) (xs ++ ys).
    Proof.
      intros * Hnodup Heq *. split.
      - rewrite Senv.HasClock_app. intros [Hin | Hin].
        + apply Env.In_find_adds'; eauto using NoDupMembers_map, NoDupMembers_app_l.
          inv Hin. solve_In.
        + assert (Hin' := Hin). apply Heq in Hin.
          rewrite Env.gsso'; auto.
          inv Hin'. intros In1. simpl_In.
          eapply NoDupMembers_app_InMembers; eauto using In_InMembers.
      - intros Hfind.
        apply Env.find_env_from_list' in Hfind as [Hin| [Hin Hfind]]; apply Senv.HasClock_app; [left|right].
        + simpl_In. econstructor; eauto.
        + apply Heq in Hfind; auto.
    Qed.

    Lemma envs_eq_inout {PSyn prefs} (n : @L.node PSyn prefs) :
      envs_eq
        (Env.adds' (idsnd (idfst (L.n_in n)))
           (Env.from_list (idsnd (idfst (idfst (L.n_out n))))))
        (Senv.senv_of_ins (L.n_in n) ++ Senv.senv_of_decls (L.n_out n)).
    Proof.
      assert (NoDupMembers (Senv.senv_of_decls (L.n_out n))) as ND1.
      { eapply NoDupMembers_app_r, L.node_NoDupMembers. }
      apply env_eq_env_from_list in ND1 as Env1.
      eapply env_eq_env_adds' in Env1; eauto using L.node_NoDupMembers.
      unfold Senv.idck, Senv.senv_of_decls, Senv.senv_of_ins, idfst, idsnd in *. rewrite ? map_map in *.
      erewrite map_ext with (l:=L.n_in _), map_ext with (l:=L.n_out _) in Env1; eauto.
      all:unfold L.decl; intros; destruct_conjs; auto.
    Qed.

    Lemma envs_eq_node {PSyn prefs} (n : @L.node PSyn prefs) locs blks :
      L.n_block n = L.Blocal (L.Scope locs blks) ->
      envs_eq
        (Env.adds' (idsnd (idfst (idfst locs)))
                   (Env.adds' (idsnd (idfst (L.n_in n)))
                              (Env.from_list (idsnd (idfst (idfst (L.n_out n)))))))
        (Senv.senv_of_ins (L.n_in n) ++ Senv.senv_of_decls (L.n_out n) ++ Senv.senv_of_decls locs).
    Proof.
      intros Hblk.
      pose proof (L.n_nodup n) as (Hnd1&Hnd2). rewrite Hblk in *; clear Hblk.
      inv Hnd2.
      rewrite app_assoc. apply envs_eq_app_comm.
      pose proof (envs_eq_inout n) as Env1.
      eapply env_eq_env_adds' with (xs:=Senv.senv_of_decls locs) in Env1.
      2:{ inv H1.
          apply NoDupMembers_app; auto using L.node_NoDupMembers.
          - apply Senv.NoDupMembers_senv_of_decls; auto.
          - intros * In1 In2. simpl_In. eapply H5; eauto using In_InMembers.
            rewrite in_app_iff in *. destruct Hin; [left|right]; solve_In. }
      unfold Senv.idck, Senv.senv_of_decls, Senv.senv_of_ins, idfst, idsnd in *. rewrite ? map_map in *.
      erewrite map_ext with (l:=locs) in Env1; eauto.
      all:unfold L.decl; intros; destruct_conjs; auto.
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
      intros. cases_eqn HH.
      now rewrite equiv_decb_refl, Pos.eqb_refl in HH0.
    Qed.

    Lemma common_suffix_app_l :
      forall l l1 l2,
        length l2 < length l1 ->
        common_suffix l1 l2 = common_suffix (l1 ++ l) l2.
    Proof.
      induction l1; simpl; intros * Hlen.
      - inv Hlen.
      - cases_eqn HH. f_equal. apply IHl1. simpl in Hlen. lia.
    Qed.

    Lemma clock_parent_length :
      forall ck ck',
        clock_parent ck ck' ->
        length (suffix_of_clock ck []) < length (suffix_of_clock ck' []).
    Proof.
      induction 1; simpl;
        setoid_rewrite <- app_nil_l at 4;
        setoid_rewrite suffix_of_clock_app;
        rewrite length_app; simpl; lia.
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
    Hint Constructors prefix : datatypes.

    Lemma prefix_app:
      forall {A} (l l' : list A), prefix l (l ++ l').
    Proof.
      induction l; simpl; auto with datatypes.
    Qed.

    Lemma prefix_app':
      forall {A} (l l1 l2 : list A), prefix l l1 -> prefix l (l1 ++ l2).
    Proof.
      induction 1; simpl; auto with datatypes.
    Qed.

    Lemma prefix_refl :
      forall {A} (l : list A), prefix l l.
    Proof. induction l; auto with datatypes. Qed.

    Lemma prefix_app3 :
      forall {A} (l1 l2 : list A) e,
        prefix l1 (l2 ++ [e]) ->
        prefix l1 l2 \/ l1 = (l2 ++ [e]).
    Proof.
      intros * Hp. generalize dependent l1.
      induction l2; simpl; intros.
      - inv Hp; auto with datatypes. inv H1; auto.
      - inv Hp; auto with datatypes. specialize (IHl2 _ H1) as []; auto with datatypes.
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
      - intro Hp. generalize dependent bk.
        induction ck; intros.
        + simpl in *. inv Hp. destruct bk; simpl in *; auto.
          setoid_rewrite <- app_nil_l in H0 at 3.
          rewrite suffix_of_clock_app in H0.
          now apply app_cons_not_nil in H0.
        + simpl in *.
          setoid_rewrite <- app_nil_l in Hp at 4.
          rewrite suffix_of_clock_app in Hp.
          apply prefix_app3 in Hp as [Hp|Heq].
          specialize (IHck _ Hp) as []; subst; auto with clocks.
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
      intros. generalize dependent sfx2.
      induction H as [|a]. auto with datatypes. intros * Hp. simpl. destruct a.
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
      generalize dependent c. induction lck. simpl. intros.
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
    intros ? [].
    induction nodes; intros * Hnames Htog; inv Hnames; monadInv Htog;
      simpl in EQ; monadInv EQ; constructor; simpl; auto.
    - erewrite to_node_name in H1; eauto.
    - eapply IHnodes in H2; eauto. 2:simpl; rewrite EQ; simpl; eauto.
      simpl in H2; auto.
  Qed.

  Fact to_global_types : forall G G',
      to_global G = OK G' ->
      NL.types G' = L.types G.
  Proof.
    intros [] * Htog.
    monadInv Htog; auto.
  Qed.

  Fact to_global_externs : forall G G',
      to_global G = OK G' ->
      NL.externs G' = L.externs G.
  Proof.
    intros [] * Htog.
    monadInv Htog; auto.
  Qed.

  Fact vars_of_spec: forall es xr,
      vars_of es = Some xr <->
      Forall2 (fun e '(x, ck) => exists ty, e = L.Evar x (ty, ck)) es xr.
  Proof.
    induction es; intros *; simpl in *; split; intros H.
    - inv H; auto.
    - inv H; auto.
    - destruct a; inv H.
      destruct a as (?&?). cases; inv H1.
      constructor; eauto. eapply IHes; eauto.
    - inv H. destruct y, H2 as (?&?); subst.
      eapply IHes in H4. rewrite H4; auto.
  Qed.

  Lemma vars_of_Some: forall es,
      Forall (fun e => exists x ann, e = L.Evar x ann) es ->
      exists xr, vars_of es = Some xr.
  Proof.
    induction es; intros F; inv F.
    - exists []; auto.
    - eapply IHes in H2 as (xr&?).
      destruct H1 as (?&(?&?)&?); subst.
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

  Fact to_controls_fst {A} errmsg : forall (es : list (A * _)) es',
      mmap (fun '(i, es) => match es with
                            | [e] => do ce <- to_cexp e; OK (i, ce)
                            | _ => Error errmsg
                         end) es = OK es' ->
      map fst es' = map fst es.
  Proof.
    unfold mmap.
    induction es; intros * Hmap; monadInv1 Hmap; auto.
    cases_eqn EQ. monadInv EQ. simpl.
    f_equal; auto.
  Qed.

  (** *** Some sorting properties *)

  Fact Permutation_seq_eq : forall n xs,
      Permutation xs (seq 0 n) ->
      Sorted.StronglySorted le xs ->
      xs = seq 0 n.
  Proof.
    intros n xs.
    assert (Forall (fun x => 0 <= x) xs) as Hf.
    { eapply Forall_forall; intros. lia. }
    revert xs Hf.
    generalize 0 as start.
    induction n; intros * Hf Hperm Hs; simpl in *.
    - apply Permutation_sym, Permutation_nil in Hperm; subst; auto.
    - destruct xs. 1:apply Permutation_nil in Hperm; congruence.
      inv Hf. inv Hs.
      assert (n0 = start); subst.
      { assert (In start (n0::xs)) as Hin by (rewrite Hperm; auto with datatypes).
        inv Hin; auto.
        eapply Forall_forall in H4; eauto. lia. }
      f_equal.
      apply Permutation_cons_inv in Hperm; auto.
      eapply IHn; eauto.
      rewrite Forall_forall in *; intros * Hin.
      rewrite Hperm, in_seq in Hin. lia.
  Qed.

  (** *** Some properties of complete_branches *)

  Lemma complete_branches_In : forall k e n es,
      In (k, Some e) (complete_branches n es) ->
      In (k, e) es.
  Proof.
    induction n; intros * Hin; simpl in *.
    - eapply in_map_iff in Hin as ((?&?)&Heq&?); inv Heq; auto.
    - destruct es as [|(?&?)]; simpl in *.
      + destruct Hin; eauto. inv H.
        eapply IHn in H; eauto.
      + destruct (e0 =? a); inv Hin; eauto.
        * inv H; eauto.
        * inv H.
        * eapply IHn in H; eauto.
  Qed.

  Lemma complete_branches_fst : forall n es,
      NoDupMembers es ->
      Sorted.StronglySorted (fun es1 es2 => le (fst es1) (fst es2)) es ->
      incl (map fst es) (seq 0 n) ->
      map fst (complete_branches (seq 0 n) es) = (seq 0 n).
  Proof.
    intros n. generalize 0 as start.
    induction n; intros * Hnd Hsort Hincl; simpl in *.
    - apply incl_nil, map_eq_nil in Hincl; subst; auto.
    - destruct es as [|(?&?)]; inv Hnd; inv Hsort; simpl in *; auto.
      + f_equal; eauto using incl_nil', Sorted.StronglySorted with datatypes.
      + destruct (n0 =? start) eqn:Hn; simpl.
        * eapply Nat.eqb_eq in Hn; subst.
          f_equal; auto.
          eapply IHn; eauto.
          apply incl_cons' in Hincl as (?&Hincl).
          intros ? Hin. assert (Hin':=Hin). apply Hincl in Hin'; inv Hin'; auto.
          exfalso. now apply H1, fst_InMembers.
        * eapply Nat.eqb_neq in Hn.
          f_equal; auto.
          eapply IHn; simpl. 1,2:constructor; simpl in *; eauto.
          apply incl_cons' in Hincl as (?&Hincl).
          apply incl_cons.
          -- inv H; auto. congruence.
          -- intros ? Hin. assert (Hin':=Hin). apply Hincl in Hin'; inv Hin'; auto.
             exfalso.
             eapply in_map_iff in Hin as (?&?&Hin); subst.
             eapply Forall_forall in H4; eauto.
             inv H; try congruence.
             eapply in_seq in H0 as (Hle1&Hle2). lia.
  Qed.

End TR.

Module TrFun
       (Ids   : IDS)
       (Op    : OPERATORS)
       (OpAux : OPERATORS_AUX Ids Op)
       (Cks   : CLOCKS   Ids Op OpAux)
       (Senv  : STATICENV Ids Op OpAux Cks)
       (L     : LSYNTAX  Ids Op OpAux Cks Senv)
       (CE    : CESYNTAX Ids Op OpAux Cks)
       (NL    : NLSYNTAX Ids Op OpAux Cks CE)
       <: TR Ids Op OpAux Cks Senv L CE NL.
  Include TR Ids Op OpAux Cks Senv L CE NL.
End TrFun.
