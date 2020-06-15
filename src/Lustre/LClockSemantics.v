From Coq Require Import List.
Import List.ListNotations.
Open Scope list_scope.

From Coq Require Import Streams.
From Coq Require Import Sorting.Permutation.
From Coq Require Import Setoid.
From Coq Require Import Morphisms.

From Coq Require Import FSets.FMapPositive.
From Velus Require Import Common.
From Velus Require Import CommonList.
From Velus Require Import Environment.
From Velus Require Import Operators.
From Velus Require Import Clocks.
From Velus Require Import Lustre.LSyntax Lustre.LTyping Lustre.LClocking Lustre.LOrdered Lustre.LSemantics.
From Velus Require Import CoindStreams.

Local Set Warnings "-masking-absolute-name".
Module Type LCLOCKSEMANTICS
       (Import Ids : IDS)
       (Import Op : OPERATORS)
       (Import OpAux : OPERATORS_AUX Op)
       (Import Syn : LSYNTAX Ids Op)
       (Import Typ : LTYPING Ids Op Syn)
       (Import Clo : LCLOCKING Ids Op Syn)
       (Import Lord : LORDERED Ids Op Syn)
       (Import Str : COINDSTREAMS Op OpAux)
       (Import Sem : LSEMANTICS Ids Op OpAux Syn Lord Str).

  Definition history_tl (H: history) : history :=
    Env.map (@tl value) H.

  Fact history_tl_find_Some : forall (H: history) id vs,
      Env.find id H = Some vs ->
      Env.find id (history_tl H) = Some (tl vs).
  Proof.
    intros H id vs Hfind.
    unfold history_tl.
    rewrite Env.Props.P.F.map_o.
    rewrite Hfind. reflexivity.
  Qed.

  Fact history_tl_find_Some' : forall (H: history) id vs,
      Env.find id (history_tl H) = Some vs ->
      exists v, Env.find id H = Some (v ⋅ vs).
  Proof.
    intros H id vs Hfind.
    unfold history_tl in Hfind.
    rewrite Env.Props.P.F.map_o in Hfind.
    apply option_map_inv_Some in Hfind as [vs' [Hfind Htl]]; subst.
    exists (hd vs'). destruct vs'; auto.
  Qed.

  Fact history_tl_find_None : forall (H: history) id,
      Env.find id H = None ->
      Env.find id (history_tl H) = None.
  Proof.
    intros H id Hfind.
    unfold history_tl.
    rewrite Env.Props.P.F.map_o.
    rewrite Hfind. reflexivity.
  Qed.

  Fact history_tl_find_None' : forall (H: history) id,
      Env.find id (history_tl H) = None ->
      Env.find id H = None.
  Proof.
    intros H id Hfind.
    unfold history_tl in Hfind.
    rewrite Env.Props.P.F.map_o in Hfind.
    apply option_map_inv_None in Hfind; auto.
  Qed.

  Definition env := Env.t value.

  Definition history_nth (n : nat) (H: history) : env :=
    Env.map (Str_nth n) H.

  Definition history_hd (H: history) : env := history_nth 0 H.

  Lemma history_nth_tl : forall H n,
      history_nth (S n) H = history_nth n (history_tl H).
  Proof.
    intros H n.
    unfold history_nth, history_tl.
    rewrite Env.map_map. eapply Env.map_ext.
    intros [x xs]. rewrite Str_nth_S; auto.
  Qed.

  Fact history_nth_find_Some : forall n (H: history) id vs,
      Env.find id H = Some vs ->
      Env.find id (history_nth n H) = Some (Str_nth n vs).
  Proof.
   induction n; intros H id vs Hfind.
   - unfold history_nth.
     rewrite Env.Props.P.F.map_o, Hfind. reflexivity.
   - rewrite history_nth_tl.
     rewrite IHn with (vs:=(tl vs)); auto.
     erewrite history_tl_find_Some; auto.
  Qed.

  Fact history_nth_find_Some' : forall n (H: history) id v,
      Env.find id (history_nth n H) = Some v ->
      exists vs, Env.find id H = Some vs /\ vs # n = v.
  Proof.
   induction n; intros H id v Hfind.
   - unfold history_nth in Hfind.
     rewrite Env.Props.P.F.map_o in Hfind.
     apply option_map_inv_Some in Hfind as [vs' [Hfind Heq]].
     exists vs'; auto.
   - rewrite history_nth_tl in Hfind.
     apply IHn in Hfind as [vs' [Hfind Heq]].
     apply history_tl_find_Some' in Hfind as [v' Hfind].
     exists (v' ⋅ vs'); split; auto.
  Qed.

  Fact history_nth_find_None : forall n (H: history) id,
      Env.find id H = None ->
      Env.find id (history_nth n H) = None.
  Proof.
   induction n; intros H id Hfind.
   - unfold history_nth.
     rewrite Env.Props.P.F.map_o, Hfind. reflexivity.
   - rewrite history_nth_tl.
     rewrite IHn; auto.
     erewrite history_tl_find_None; auto.
  Qed.

  Fact history_nth_find_None' : forall n (H: history) id,
      Env.find id (history_nth n H) = None ->
      Env.find id H = None.
  Proof.
   induction n; intros H id Hfind.
   - unfold history_nth in Hfind.
     rewrite Env.Props.P.F.map_o in Hfind.
     apply option_map_inv_None in Hfind; auto.
   - rewrite history_nth_tl in Hfind.
     apply IHn in Hfind.
     apply history_tl_find_None' in Hfind; auto.
  Qed.

  (** *** Interpreter *)
  Fixpoint interp_clock_instant R base ck : bool :=
    match ck with
    | Cbase => base
    | Con ck id b =>
      let b' := interp_clock_instant R base ck in
      match Env.find id R with
      | Some v => match v with
                  | OpAux.present v =>
                    match OpAux.val_to_bool v with
                    | Some true => andb b b'
                    | Some false => andb (negb b) b'
                    | _ => false
                    end
                  | _ => false
                  end
      | None => false
      end
    end.

  CoFixpoint interp_clock H base ck : Stream bool :=
    match base with
    | b ⋅ base =>
      (interp_clock_instant (history_hd H) b ck) ⋅ (interp_clock (history_tl H) base ck)
    end.

  Fact interp_clock_Cons : forall H b bs ck,
      interp_clock H (b ⋅ bs) ck ≡ (interp_clock_instant (history_hd H) b ck) ⋅ (interp_clock (history_tl H) bs ck).
  Proof.
    intros H b bs ck; simpl.
    constructor; simpl; reflexivity.
  Qed.

  Lemma interp_clock_nth : forall n H base ck,
      (interp_clock H base ck) # n = interp_clock_instant (history_nth n H) (base # n) ck.
  Proof.
    induction n; intros H [b base] ck; rewrite interp_clock_Cons; simpl.
    - repeat rewrite Str_nth_0. reflexivity.
    - repeat rewrite Str_nth_S.
      rewrite IHn, <- history_nth_tl. reflexivity.
  Qed.

  Definition wt_value (ty : type) (v : value) :=
    match v with
    | absent => True
    | present v => wt_val v ty
    end.

  Definition wt_env_val (R : env) (xty : ident * type) :=
    match Env.find (fst xty) R with
    | None => False
    | Some v => wt_value (snd xty) v
    end.

  Definition wt_env (vars : list (ident * type)) (R : env) :=
    Forall (wt_env_val R) vars.

  Definition wt_hist_val (H : history) (xty : ident * type) :=
    match Env.find (fst xty) H with
    | None => False
    | Some vs => SForall (wt_value (snd xty)) vs
    end.

  Definition wt_hist (vars : list (ident * type)) (H : history) :=
    Forall (wt_hist_val H) vars.

  Fact wt_hist_wt_env : forall vars hist,
      wt_hist vars hist ->
      forall n, wt_env vars (history_nth n hist).
  Proof.
    intros vars hist Hwt n.
    unfold wt_hist, wt_env in *.
    eapply Forall_impl; [|eauto]; clear Hwt.
    intros [x ty] Hwt.
    unfold wt_hist_val, wt_env_val in *; simpl in *.
    destruct (Env.find x hist) eqn:Hfind; [|inv Hwt].
    apply history_nth_find_Some with (n:=n) in Hfind; rewrite Hfind.
    rewrite SForall_forall in Hwt; auto.
  Qed.

  Fact history_hd_refines : forall H H',
      Env.refines eq H H' ->
      Env.refines eq (history_hd H) (history_hd H').
  Proof.
    intros H H' Href x v Hfind.
    eapply history_nth_find_Some' in Hfind as [vs' [Hfind Heq]].
    exists v; split; auto.
    eapply Href in Hfind as [vs'' [? Hfind]]; subst.
    eapply history_nth_find_Some in Hfind; eauto.
  Qed.

  Fact history_tl_refines : forall H H',
      Env.refines eq H H' ->
      Env.refines eq (history_tl H) (history_tl H').
  Proof.
    intros H H' Href x vs Hfind.
    eapply history_tl_find_Some' in Hfind as [v' Hfind].
    eapply Href in Hfind as [vs' [Heq' Hfind']].
    exists (tl vs').
    apply history_tl_find_Some in Hfind'.
    split; auto.
    destruct vs'; simpl. inv Heq'; auto.
  Qed.

  Lemma history_nth_refines : forall H H',
      Env.refines eq H H' ->
      forall n, Env.refines eq (history_nth n H) (history_nth n H').
  Proof.
    intros H H' Href n; revert H H' Href.
    induction n; intros.
    - apply history_hd_refines, Href.
    - repeat rewrite history_nth_tl.
      apply IHn, history_tl_refines, Href.
  Qed.

  Fact history_nth_add : forall H n id vs,
      Env.Equal (history_nth n (Env.add id vs H)) (Env.add id (vs # n) (history_nth n H)).
  Proof.
    intros H n id vs id'.
    destruct Env.find eqn:Hfind; symmetry.
    - eapply history_nth_find_Some' in Hfind as [vs' [? Hfind]]; subst.
      destruct (ident_eqb id id') eqn:Heq.
      + rewrite ident_eqb_eq in Heq; subst.
        rewrite Env.gss in *.
        inv H0. auto.
      + rewrite ident_eqb_neq in Heq.
        rewrite Env.gso in *; auto.
        eapply history_nth_find_Some in H0; eauto.
    - eapply history_nth_find_None' in Hfind.
      destruct (ident_eqb id id') eqn:Heq.
      + rewrite ident_eqb_eq in Heq; subst.
        rewrite Env.gss in *. inv Hfind.
      + rewrite ident_eqb_neq in Heq.
        rewrite Env.gso in *; auto.
        eapply history_nth_find_None; auto.
  Qed.

  Fact interp_clock_instant_refines : forall R R' vars ck base,
      wt_env vars R ->
      wt_clock vars ck ->
      Env.refines eq R R' ->
      interp_clock_instant R base ck = interp_clock_instant R' base ck.
  Proof with eauto.
    induction ck; intros * Henv Hck Href; simpl in *; inv Hck.
    - reflexivity.
    - specialize (IHck base Henv H4 Href).
      unfold wt_env in Henv; rewrite Forall_forall in Henv.
      eapply Henv in H2; unfold wt_env_val in H2; simpl in H2.
      destruct (Env.find i R) eqn:Hfind.
      + apply Href in Hfind as [v' [? Hfind]]; subst. rewrite Hfind.
        destruct v'; [auto|].
        destruct (val_to_bool v); auto. repeat rewrite IHck. reflexivity.
      + inv H2.
  Qed.

  Lemma interp_clock_refines : forall H H' vars ck base,
      wt_hist vars H ->
      wt_clock vars ck ->
      Env.refines eq H H' ->
      interp_clock H base ck ≡ interp_clock H' base ck.
  Proof with eauto.
    intros * Hhist Hck Href.
    eapply ntheq_eqst; intros n.
    repeat rewrite interp_clock_nth.
    eapply interp_clock_instant_refines...
    - eapply wt_hist_wt_env...
    - eapply history_nth_refines...
  Qed.

  Fact interp_clock_instant_add : forall R id v ck base,
      ~Is_free_in_clock id ck ->
      interp_clock_instant (Env.add id v R) base ck = interp_clock_instant R base ck.
  Proof.
    induction ck; intros base Hnin; simpl; auto.
    rewrite Env.gso.
    - destruct Env.find as [[|v']|]; auto.
      destruct val_to_bool as [[|]|]; f_equal; auto.
      1,2:rewrite IHck; auto.
      1,2:intro contra; apply Hnin; constructor; auto.
    - intro contra; subst. apply Hnin. constructor.
  Qed.

  Instance interp_clock_instant_Proper:
    Proper (@Env.Equal value ==> @eq bool ==> @eq clock ==> @eq bool)
           interp_clock_instant.
  Proof.
    intros H H' Hequal base' base ? ck' ck ?; subst.
    induction ck; simpl; auto.
    - destruct Env.find as [[|v]|] eqn:Hfind;
        rewrite Hequal in Hfind; rewrite Hfind; auto.
      rewrite IHck; auto.
  Qed.

  Lemma interp_clock_add : forall H id vs ck base,
      ~Is_free_in_clock id ck ->
      interp_clock (Env.add id vs H) base ck ≡ interp_clock H base ck.
  Proof.
    intros * Hisfree.
    eapply ntheq_eqst; intros n.
    repeat rewrite interp_clock_nth.
    rewrite history_nth_add.
    apply interp_clock_instant_add; auto.
  Qed.

  (** Synchronization (alignement ?) *)

  CoInductive synchronized: Stream value -> Stream bool -> Prop :=
  | synchro_present:
      forall v vs bs,
        synchronized vs bs ->
        synchronized (present v ⋅ vs) (true ⋅ bs)
  | synchro_absent:
      forall vs bs,
        synchronized vs bs ->
        synchronized (absent ⋅ vs) (false ⋅ bs).

  Lemma synchronized_spec : forall vs bs,
      synchronized vs bs <->
      (forall n, (exists v, bs # n = true /\ vs # n = present v)
            \/ (bs # n = false /\ vs # n = absent)).
  Proof with eauto.
    split.
    - intros H n. revert vs bs H.
      induction n; intros.
      + inv H; repeat rewrite Str_nth_0.
        * left. exists v...
        * right...
      + inv H; repeat rewrite Str_nth_S...
    - revert vs bs.
      cofix CoFix; intros * H.
      unfold_Stv vs; unfold_Stv bs.
      1,4:(specialize (H 0); repeat rewrite Str_nth_0 in H;
           destruct H as [[? [? ?]]|[? ?]]; try congruence).
      1,2:(constructor; cofix_step CoFix H).
  Qed.

  Lemma const_synchronized : forall bs c,
      synchronized (const bs c) bs.
  Proof with eauto.
    intros bs c.
    remember (const bs c) as vs.
    rewrite synchronized_spec. intros n.
    eapply eq_EqSt, const_spec with (n:=n) in Heqvs.
    rewrite Heqvs; clear Heqvs.
    destruct (bs # n).
    - left. eexists...
    - right...
  Qed.

End LCLOCKSEMANTICS.


Module LClockSemanticsFun
       (Ids : IDS)
       (Op : OPERATORS)
       (OpAux : OPERATORS_AUX Op)
       (Syn : LSYNTAX Ids Op)
       (Typ : LTYPING Ids Op Syn)
       (Clo : LCLOCKING Ids Op Syn)
       (Lord : LORDERED Ids Op Syn)
       (Str : COINDSTREAMS Op OpAux)
       (Sem : LSEMANTICS Ids Op OpAux Syn Lord Str) <: LCLOCKSEMANTICS Ids Op OpAux Syn Typ Clo Lord Str Sem.
  Include LCLOCKSEMANTICS Ids Op OpAux Syn Typ Clo Lord Str Sem.
End LClockSemanticsFun.
