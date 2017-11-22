Require Import List.
Import List.ListNotations.
Open Scope list_scope.
Require Import Coq.Sorting.Permutation.
Require Import Morphisms.

Require Import Coq.FSets.FMapPositive.
Require Import Velus.Common.
Require Import Velus.Operators.
Require Import Velus.Clocks.
Require Import Velus.NLustre.NLSyntax.
Require Import Velus.NLustre.NLSemanticsCommon.
Require Import Velus.NLustre.Ordered.
Require Import Streams.

Require Import Velus.NLustre.NLSemanticsCoIndWire.
Require Import Velus.NLustre.NLSemanticsCoInd.

Require Import Setoid.
Module Type SEMEQUIV
       (Import Ids   : IDS)
       (Import Op    : OPERATORS)
       (Import OpAux : OPERATORS_AUX Op)
       (Import Clks  : CLOCKS    Ids)
       (Import Syn   : NLSYNTAX  Ids Op Clks)
       (Import Comm  : NLSEMANTICSCOMMON Ids Op OpAux Clks Syn)
       (Import Ord   : ORDERED   Ids Op Clks Syn)
       (Wire         : NLSEMANTICSCOINDWIRE Ids Op OpAux Clks Syn Comm Ord)
       (Mod          : NLSEMANTICSCOIND Ids Op OpAux Clks Syn Comm Ord).

  CoFixpoint false_s : Stream bool := false ::: false_s.

  Lemma unfold_false_s : false_s = false ::: false_s.
  Proof.
    rewrite unfold_Stream at 1; auto.
  Qed.

  Section Global.

    Variable G: global.

    Remark fby1_equiv:
      forall c v xs,
        Wire.fby1 false_s v (sem_const c) xs ≡ Mod.fby1 v (sem_const c) xs.
    Proof.
      cofix; intros.
      unfold_Stv xs; constructor; simpl; auto.
    Qed.

    Corollary fby_equiv:
      forall c xs,
        Wire.fby false_s (sem_const c) xs ≡ Mod.fby (sem_const c) xs.
    Proof.
      cofix; intros.
      unfold_Stv xs; constructor; simpl; auto.
      apply fby1_equiv.
    Qed.

    Remark merge_reset_with_false:
      forall r, Wire.merge_reset false_s r ≡ r.
    Proof.
      cofix; intro.
      rewrite unfold_false_s.
      destruct r.
      constructor; simpl; auto.
    Qed.

    (* CoInductive synchronised: Stream value -> Stream value -> Prop := *)
    (* | A_synchro: *)
    (*     forall xs ys, *)
    (*       synchronised xs ys -> *)
    (*       synchronised (absent ::: xs) (absent ::: ys) *)
    (* | P_synchro: *)
    (*     forall xs ys x y, *)
    (*       synchronised xs ys -> *)
    (*       synchronised (present x ::: xs) (present y ::: ys). *)

    (* Ltac prove_synchro := *)
    (*   match goal with *)
    (*     |- forall s, synchronised s ?s' => *)
    (*     let COFIX := fresh "COFIX" in *)
    (*     let s := fresh s in *)
    (*     let v := fresh "v" in *)
    (*     cofix COFIX; intro s; *)
    (*     rewrite unfold_Stream; *)
    (*     destruct s as [v]; destruct v; simpl; constructor; auto *)
    (*   end. *)

    (* Lemma when_witness: *)
    (*   forall k xs ys, *)
    (*     synchronised xs ys -> *)
    (*     exists rs, when k xs ys rs. *)
    (* Proof. *)
    (*   eexists. *)
    (*   revert k xs ys H. *)
    (*   cofix. *)
    (*   intros. *)
    (*   inv H. *)
    (*   - constructor. *)
    (* Admitted. *)

    (* Lemma flatten_masks_n_spec: *)
    (*   forall rs xs n, *)
    (*     Mod.flatten_masks rs (Mod.masks_from n rs xs) ≡ xs. *)
    (* Proof. *)
    (*   cofix; intros. *)
    (*   unfold_Stv rs; unfold_St xs. *)
    (*   - constructor; simpl; auto. *)
    (*     simpl. *)

    Lemma flatten_masks_spec:
      forall rs xs,
        Mod.flatten_masks rs (Mod.masks rs xs) ≡ xs.
    Proof.
      cofix; intros.
      unfold_Stv rs; unfold_St xs.
      - constructor; simpl; auto.
        admit.
      - constructor; simpl; auto.
        admit.
    Admitted.

    Definition map_history (f: Stream value -> Stream value) (H: history) : history :=
      PM.map f H.

    Fact map_history_spec:
      forall H x xs f,
        Proper (@EqSt value ==> @EqSt value) f ->
        sem_var H x xs ->
        sem_var (map_history f H) x (f xs).
    Proof.
      induction 2 as [? ? xs xs' Sem Exs].
      econstructor.
      - apply PM.map_1; eauto.
      - rewrite Exs; reflexivity.
    Qed.

    Definition mask_history (n: nat) (rs: Stream bool) (H: history) : history :=
      map_history (Mod.mask_v n rs) H.

    Corollary mask_history_spec:
      forall n rs H x xs,
        sem_var H x xs ->
        sem_var (mask_history n rs H) x (Mod.mask_v n rs xs).
    Proof.
      intros; apply map_history_spec; auto.
      solve_proper.
    Qed.

    Corollary mask_history_spec_Forall2:
      forall n rs H xs xss,
        Forall2 (sem_var H) xs xss ->
        Forall2 (sem_var (mask_history n rs H)) xs (List.map (Mod.mask_v n rs) xss).
    Proof.
      intros.
      rewrite Forall2_map_2.
      eapply Forall2_impl_In; eauto.
      intros; apply mask_history_spec; auto.
    Qed.

    Remark const_false_absent:
      forall c,
        const c false_s ≡ Streams.const absent.
    Proof.
      cofix; constructor; simpl; auto.
    Qed.

    (* Remark mask_absent: *)
    (*   forall n rs, *)
    (*     Mod.mask n rs (Streams.const absent) ≡ Streams.const absent. *)
    (* Proof. *)
    (*   cofix; intros. *)
    (*   unfold_Stv rs; constructor; destruct n as [|[]]; *)
    (*     simpl; auto; reflexivity. *)
    (* Qed. *)




    (* Remark clocks_of_nil: *)
    (*   clocks_of [] ≡ false_s. *)
    (* Proof. *)
    (*   cofix; constructor; simpl; auto. *)
    (* Qed. *)

    Remark mask_sem_const:
      forall n rs c b,
        Mod.mask_v n rs (const c b) ≡ const c (Mod.mask_b n rs b).
    Proof.
      cofix; intros.
      unfold_Stv rs; unfold_Stv b; destruct n as [|[]];
        constructor; simpl; auto;
          rewrite const_false_absent; reflexivity.
    Qed.

    Remark when_absent:
      forall k, when k (Streams.const absent) (Streams.const absent) (Streams.const absent).
    Proof.
      cofix;
        rewrite (unfold_Stream (Streams.const absent));
        simpl; constructor; auto.
    Qed.

    Corollary when_mask:
      forall n rs k es xs os,
        when k es xs os ->
        when k (Mod.mask_v n rs es) (Mod.mask_v n rs xs) (Mod.mask_v n rs os).
    Proof.
      cofix; intros.
      rewrite (unfold_Stream (Mod.mask_v n rs es));
        rewrite (unfold_Stream (Mod.mask_v n rs xs));
        rewrite (unfold_Stream (Mod.mask_v n rs os)).
      unfold_Stv rs; unfold_Stv es; unfold_St xs; unfold_St os;
        destruct n as [|[]]; try (now inv H; constructor; auto).
      rewrite <-unfold_Stream; apply when_absent.
      rewrite <-unfold_Stream; apply when_absent.
    Qed.

    Remark lift1_absent:
      forall op t, lift1 op t (Streams.const absent) (Streams.const absent).
    Proof.
      cofix;
        rewrite (unfold_Stream (Streams.const absent));
        simpl; constructor; auto.
    Qed.

    Corollary lift1_mask:
      forall n rs op t es os,
        lift1 op t es os ->
        lift1 op t (Mod.mask_v n rs es) (Mod.mask_v n rs os).
    Proof.
      cofix; intros.
      rewrite (unfold_Stream (Mod.mask_v n rs es));
        rewrite (unfold_Stream (Mod.mask_v n rs os)).
      unfold_Stv rs; unfold_Stv es; unfold_St os;
        destruct n as [|[]]; try (now inv H; constructor; auto).
      rewrite <-unfold_Stream; apply lift1_absent.
      rewrite <-unfold_Stream; apply lift1_absent.
    Qed.

    Remark lift2_absent:
      forall op t1 t2, lift2 op t1 t2 (Streams.const absent) (Streams.const absent) (Streams.const absent).
    Proof.
      cofix;
        rewrite (unfold_Stream (Streams.const absent));
        simpl; constructor; auto.
    Qed.

    Corollary lift2_mask:
      forall n rs op t1 t2 e1s e2s os,
        lift2 op t1 t2 e1s e2s os ->
        lift2 op t1 t2 (Mod.mask_v n rs e1s) (Mod.mask_v n rs e2s) (Mod.mask_v n rs os).
    Proof.
      cofix; intros.
      rewrite (unfold_Stream (Mod.mask_v n rs e1s));
        rewrite (unfold_Stream (Mod.mask_v n rs e2s));
        rewrite (unfold_Stream (Mod.mask_v n rs os)).
      unfold_Stv rs; unfold_Stv e1s; unfold_Stv e2s; unfold_St os;
        destruct n as [|[]]; try (now inv H; constructor; auto).
      rewrite <-unfold_Stream; apply lift2_absent.
      rewrite <-unfold_Stream; apply lift2_absent.
    Qed.

    Lemma mask_sem_lexp:
      forall n rs H b e es,
        sem_lexp H b e es ->
        sem_lexp (mask_history n rs H) (Mod.mask_b n rs b) e (Mod.mask_v n rs es).
    Proof.
      intros ** Sem; induction Sem.
      - constructor; rewrite H0; apply mask_sem_const.
      - constructor; apply mask_history_spec; auto.
      - econstructor; eauto.
        + apply mask_history_spec; eauto.
        + now apply when_mask.
      - econstructor; eauto.
        now apply lift1_mask.
      - econstructor; eauto.
        now apply lift2_mask.
    Qed.

     Remark merge_absent:
      merge (Streams.const absent) (Streams.const absent) (Streams.const absent) (Streams.const absent).
    Proof.
      cofix;
        rewrite (unfold_Stream (Streams.const absent));
        simpl; constructor; auto.
    Qed.

    Corollary merge_mask:
      forall n rs xs ts fs os,
        merge xs ts fs os ->
        merge (Mod.mask_v n rs xs) (Mod.mask_v n rs ts) (Mod.mask_v n rs fs) (Mod.mask_v n rs os).
    Proof.
      cofix; intros.
      rewrite (unfold_Stream (Mod.mask_v n rs xs));
        rewrite (unfold_Stream (Mod.mask_v n rs ts));
        rewrite (unfold_Stream (Mod.mask_v n rs fs));
        rewrite (unfold_Stream (Mod.mask_v n rs os)).
      unfold_Stv rs; unfold_St xs; unfold_St ts; unfold_St fs; unfold_St os;
        destruct n as [|[]]; try (now inv H; constructor; auto).
      rewrite <-unfold_Stream; apply merge_absent.
    Qed.

    Remark ite_absent:
      ite (Streams.const absent) (Streams.const absent) (Streams.const absent) (Streams.const absent).
    Proof.
      cofix;
        rewrite (unfold_Stream (Streams.const absent));
        simpl; constructor; auto.
    Qed.

    Corollary ite_mask:
      forall n rs es ts fs os,
        ite es ts fs os ->
        ite (Mod.mask_v n rs es) (Mod.mask_v n rs ts) (Mod.mask_v n rs fs) (Mod.mask_v n rs os).
    Proof.
      cofix; intros.
      rewrite (unfold_Stream (Mod.mask_v n rs es));
        rewrite (unfold_Stream (Mod.mask_v n rs ts));
        rewrite (unfold_Stream (Mod.mask_v n rs fs));
        rewrite (unfold_Stream (Mod.mask_v n rs os)).
      unfold_Stv rs; unfold_St es; unfold_St ts; unfold_St fs; unfold_St os;
        destruct n as [|[]]; try (now inv H; constructor; auto).
      rewrite <-unfold_Stream; apply ite_absent.
    Qed.

    Lemma mask_sem_cexp:
      forall n rs H b e es,
        sem_cexp H b e es ->
        sem_cexp (mask_history n rs H) (Mod.mask_b n rs b) e (Mod.mask_v n rs es).
    Proof.
      intros ** Sem; induction Sem.
      - econstructor; eauto.
        + apply mask_history_spec; eauto.
        + now apply merge_mask.
      - econstructor; eauto.
        + apply mask_sem_lexp; eauto.
        + now apply ite_mask.
      - constructor; apply mask_sem_lexp; auto.
    Qed.

    Remark fby_absent:
      forall c, Mod.fby c (Streams.const absent) ≡ Streams.const absent.
    Proof.
      cofix; intro.
      rewrite (unfold_Stream (Streams.const absent)); constructor; simpl; auto.
    Qed.

    Remark fby1_absent:
      forall v c, Mod.fby1 v c (Streams.const absent) ≡ Streams.const absent.
    Proof.
      cofix; intro.
      rewrite (unfold_Stream (Streams.const absent)); constructor; simpl; auto.
    Qed.

    (* Remark foo: *)
    (*   forall n rs c0 c xs, *)
    (*     Mod.mask absent n rs (Wire.fby1 rs c0 c xs) ≡ Mod.fby1 c0 c (Mod.mask absent n rs xs). *)
    (* Proof. *)
    (*   cofix Cofix; intros. *)
    (*   unfold_Stv rs; unfold_Stv xs; *)
    (*     constructor; destruct n as [|[]]; simpl; fold Wire.fby; auto. *)
    (*     + rewrite fby1_absent; reflexivity. *)
    (*     + rewrite fby1_absent; reflexivity. *)
    (*   - cofix Cofix; intros. *)
    (*     unfold_Stv rs; unfold_Stv xs; constructor; destruct n; *)
    (*       simpl; fold Wire.fby; auto. *)
    (*     destruct n. *)
    (*     simpl. *)
    (*     fold Wire.fby.  *)
    (*     simpl. auto. *)
    (*     simpl. auto. *)
    (*       constructor; simpl; auto. *)

    (*     rewrite <-Cofix. unfold Wire.fby1. reflexivity. *)
    Remark mask_fby:
      forall n rs c xs,
        Mod.mask_v n rs (Wire.fby rs c xs) ≡ Mod.fby c (Mod.mask_v n rs xs).
    Proof.
      cofix Cofix; intros.
      unfold_Stv rs; unfold_Stv xs; destruct n as [|[]];
        constructor; simpl; auto.
      - rewrite fby_absent; reflexivity.
      - rewrite fby_absent; reflexivity.
      - admit.
      - admit.
      - admit.
      - admit.
      - admit.
    Admitted.

    Remark clocks_of_nil_absent:
      clocks_of [] ≡ Streams.const false.
    Proof.
      cofix.
      rewrite unfold_Stream; rewrite (unfold_Stream (clocks_of [])).
      constructor; simpl; auto.
    Qed.

    (* Remark clocks_of_absent: *)
    (*   clocks_of  *)
    Remark mask_clocks_of:
      forall n rs xss,
        Mod.mask_b n rs (clocks_of xss) ≡ clocks_of (List.map (Mod.mask_v n rs) xss).
    Proof.
      cofix; intros.
      induction xss as [|xs]; simpl.
      - unfold_Stv rs; rewrite (unfold_Stream (clocks_of []));
          constructor; destruct n as [|[]]; simpl; auto;
            rewrite clocks_of_nil_absent; try apply Mod.mask_const_opaque.
        reflexivity.
      - unfold_Stv rs; unfold_Stv xs;
          constructor; destruct n as [|[]]; simpl; auto;
            try match goal with
                  |- _ = _ => clear; induction xss as [|[]]; simpl; auto
                end.
        + clear; induction xss as [|[[]]]; simpl; auto.
        + admit.
        + admit.
        + admit.
        + admit.
        + admit.
        + admit.
        + clear; induction xss as [|[[]]]; simpl; auto.
        + admit.
        + admit.
        + admit.
        + admit.
        + admit.
        + admit.
    Admitted.

    Remark reset_of_absent:
      reset_of (Streams.const absent) ≡ Streams.const false.
    Proof.
      cofix.
      rewrite unfold_Stream; rewrite (unfold_Stream (Streams.const absent)).
      constructor; simpl; auto.
    Qed.

    Remark mask_reset_of:
      forall n rs xs,
        reset_of (Mod.mask_v n rs xs) ≡ Mod.mask_b n rs (reset_of xs).
    Proof.
      cofix; intros.
      unfold_Stv rs; unfold_Stv xs;
        constructor; destruct n as [|[]]; simpl; auto;
          apply reset_of_absent.
    Qed.

    Lemma WireMod_node_reset:
      forall rs f ess oss,
        Wire.sem_node G (reset_of rs) f ess oss ->
        Mod.sem_reset G f (reset_of rs) ess oss.
    Proof.
      intros ** Reset.
      constructor.
      induction Reset
        as [? ? ? ? ? ? ? ? Sem_var
              |? ? ? ? ? ? ? ? ? ? ? Sem_vars
              |? ? ? ? ? ? ? ? ? ? ? ? ? Sem_var Sem_vars
              |? ? ? ? ? ? ? ? ? ? ? Sem_var |]
             using Wire.sem_node_mult with
          (P_equation := fun H b r e =>
                           forall i,
                             Wire.sem_equation G H b r e ->
                             Mod.sem_equation G (mask_history i r H) (Mod.mask_b i r b) e);
        intros.
      - apply (mask_history_spec i r) in Sem_var.
        econstructor; eauto.
        now apply mask_sem_cexp.
      - apply (mask_history_spec_Forall2 i r) in Sem_vars.
        econstructor; eauto.
        eapply Forall2_map_2, Forall2_impl_In; eauto.
        intros; now apply mask_sem_lexp.
      - apply (mask_history_spec i r) in Sem_var.
        apply (mask_history_spec_Forall2 i r) in Sem_vars.
        econstructor; eauto.
        instantiate (1 := List.map (Mod.mask_v i r) ess).
        + eapply Forall2_map_2, Forall2_impl_In; eauto.
          intros; apply mask_sem_lexp; auto.
        + rewrite mask_reset_of.
          constructor.
          intro n; specialize (IHReset n).
          eapply Mod.mod_sem_node_morph; eauto.
          * rewrite List.map_map.
            apply map_EqSt; try reflexivity. admit.
      - apply (mask_history_spec i r) in Sem_var.
        econstructor; eauto.
        + eapply mask_sem_lexp; eauto.
        + inv Sem_var.
          econstructor; eauto.
          now rewrite <-mask_fby.
      - econstructor; eauto.
        instantiate (1:=mask_history n0 r H).
        + now apply mask_history_spec_Forall2.
        + now apply mask_history_spec_Forall2.
        + induction (n_eqs n) as [|e]; auto.
          inversion_clear H3 as [|? ? Sem_e].
          inversion_clear H4.
          constructor; auto.
          rewrite <-mask_clocks_of; auto.
    Qed.

    Lemma WireMod_equation_node:
      (forall H b r e,
          Wire.sem_equation G H b r e ->
          (* r = false_s -> *)
          Mod.sem_equation G H b e)
      /\
      (forall r f xss oss,
          Wire.sem_node G r f xss oss ->
          Mod.sem_node G f xss oss).
    Proof.
      Check Wire.sem_equation_node_ind.
      apply Wire.sem_equation_node_ind; intros.
      - econstructor; eauto.
      - econstructor; eauto.
      - econstructor; eauto.
        eapply WireMod_node_reset; eauto.
      - econstructor; eauto.
        subst; now apply fby_equiv.
      - econstructor; eauto.
        apply Forall_impl with (2:=H4).
        auto.
    Qed.

    Theorem WireMod:
      forall G f xss yss,
        Wire.sem_node G false_s f xss yss
        <-> Mod.sem_node G f xss yss.
    Proof.
      split; intro Sem; inv Sem; econstructor; eauto; eapply Forall_impl;
        [ now apply WireMod_equation | auto
          | now apply WireMod_equation | auto ].
    Qed.

    SearchAbout Forall.

  End SEMEQUIV.
