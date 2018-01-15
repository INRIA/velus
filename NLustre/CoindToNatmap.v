Require Import List.
Import List.ListNotations.
Open Scope list_scope.
Require Import Coq.Sorting.Permutation.
Require Import Morphisms.
Require Import Coq.Program.Tactics.

Require Import Coq.FSets.FMapPositive.
Require Import Velus.Common.
Require Import Velus.Operators.
Require Import Velus.Clocks.
Require Import Velus.NLustre.NLSyntax.
Require Import Velus.NLustre.Ordered.
Require Import Velus.NLustre.Stream.
Require Import Velus.NLustre.Streams.

Require Import Velus.NLustre.NLSemantics.
Require Import Velus.NLustre.NLSemanticsCoInd.

Require Import Setoid.
Module Type COINDTONATMAP
       (Import Ids   : IDS)
       (Import Op    : OPERATORS)
       (Import OpAux : OPERATORS_AUX Op)
       (Import Clks  : CLOCKS    Ids)
       (Import Syn   : NLSYNTAX  Ids Op Clks)
       (Import Str   : STREAM        Op OpAux)
       (Import Ord   : ORDERED   Ids Op Clks Syn)
       (Indexed      : NLSEMANTICS Ids Op OpAux Clks Syn Str Ord)
       (CoInd        : NLSEMANTICSCOIND Ids Op OpAux Clks Syn Ord).

  Section Global.

    Variable G : global.

    Definition tr_stream {A} (xs: Stream A) : stream A :=
      fun n => Str_nth n xs.

    Lemma tr_stream_0:
      forall {A} (xs: Stream A) x,
        tr_stream (x ::: xs) 0 = x.
    Proof. reflexivity. Qed.

    Lemma tr_stream_S:
      forall {A} (xs: Stream A) x n,
        tr_stream (x ::: xs) (S n) = tr_stream xs n.
    Proof. reflexivity. Qed.

    Add Parametric Morphism A : (@tr_stream A)
        with signature @EqSt A ==> eq ==> eq
          as tr_stream_morph.
    Proof.
      intros xs ys Exs n.
      revert xs ys Exs; induction n; intros; destruct xs, ys; inv Exs.
      - rewrite 2 tr_stream_0; auto.
      - rewrite 2 tr_stream_S; auto.
    Qed.

    Lemma tr_stream_const:
      forall {A} (c: A) n,
        tr_stream (Streams.const c) n = c.
    Proof.
      induction n; rewrite unfold_Stream at 1; simpl.
      - now rewrite tr_stream_0.
      - now rewrite tr_stream_S.
    Qed.

    Lemma tr_stream_tl:
      forall {A} (xs: Stream A) n,
        tr_stream (tl xs) n = tr_stream xs (S n).
    Proof. reflexivity. Qed.

    (** explain all this weirdness *)
    Fixpoint tr_streams {A} (xss: list (Stream A)) : stream (list A) :=
      match xss with
      | [] => fun n => []
      | xs :: xss => fun n => tr_stream xs n :: tr_streams xss n
      end.

    Fact tr_streams_app:
      forall A (xss yss: list (Stream A)) n,
        tr_streams (xss ++ yss) n = tr_streams xss n ++ tr_streams yss n.
    Proof.
      intros; induction xss; simpl; auto.
      f_equal; auto.
    Qed.

    Lemma tr_streams_tl:
      forall xss n,
        tr_streams (List.map (tl (A:=value)) xss) n = tr_streams xss (S n).
    Proof.
      intros; induction xss; simpl; auto.
      f_equal; auto.
    Qed.

    Definition tr_history (H: CoInd.history) : Indexed.history :=
      PM.map tr_stream H.

    (** TODO: MOVE THESE TO COMMON *)
    Lemma option_map_map:
      forall {A B C} (f: A -> B) (g: B -> C) o,
        option_map g (option_map f o) = option_map (fun x => g (f x)) o.
    Proof. now destruct o. Qed.

    Lemma pm_xmapi_xmapi:
      forall {A B C} (f: A -> B) (g: B -> C) (m: PM.t A) x,
        PM.xmapi (fun _ => g) (PM.xmapi (fun _ => f) m x) x =
        PM.xmapi (fun _ (x : A) => g (f x)) m x.
    Proof.
      induction m; intro; simpl; auto.
      f_equal; auto.
      apply option_map_map.
    Qed.

    Lemma pm_map_map:
      forall {A B C} (f: A -> B) (g: B -> C) (m: PM.t A),
        PM.map g (PM.map f m) = PM.map (fun x => g (f x)) m.
    Proof.
      unfold PM.map, PM.mapi; intros.
      apply pm_xmapi_xmapi.
    Qed.

    Lemma tr_history_tl:
      forall n H,
        Indexed.restr (tr_history H) (S n) = Indexed.restr (tr_history (CoInd.history_tl H)) n.
    Proof.
      now repeat setoid_rewrite pm_map_map.
    Qed.

    Lemma sem_var_impl:
      forall H b x xs,
      CoInd.sem_var H x xs ->
      Indexed.sem_var b (tr_history H) x (tr_stream xs).
    Proof.
      intros ** Find n.
      constructor.
      inv Find.
      unfold Indexed.restr, tr_history.
      unfold PM.map.
      rewrite 2 PM.gmapi.
      erewrite PM.find_1; eauto; simpl.
      f_equal.
      apply eqst_ntheq; symmetry; auto.
    Qed.

    Corollary sem_vars_impl:
      forall H b xs xss,
      Forall2 (CoInd.sem_var H) xs xss ->
      Indexed.sem_vars b (tr_history H) xs (tr_streams xss).
    Proof.
      induction 1 as [|? ? ? ? Find];
        simpl; unfold Indexed.sem_vars, Indexed.lift; auto.
      intro; constructor; auto.
      apply sem_var_impl; auto.
    Qed.

    Lemma same_clock_impl:
      forall xss,
        CoInd.same_clock xss ->
        Indexed.same_clock (tr_streams xss).
    Proof.
      unfold Indexed.same_clock, Indexed.instant_same_clock.
      intros.
      destruct (H n) as [E|Ne].
      - left; induction xss; simpl; constructor; inv E; auto.
        apply IHxss; auto.
        eapply CoInd.same_clock_cons; eauto.
      - right; induction xss; simpl; constructor; inv Ne; auto.
        apply IHxss; eauto using CoInd.same_clock_cons.
    Qed.

    Lemma same_clock_app_impl:
      forall xss yss,
        xss <> [] ->
        yss <> [] ->
        CoInd.same_clock (xss ++ yss) ->
        forall n, Indexed.absent_list (tr_streams xss n) <-> Indexed.absent_list (tr_streams yss n).
    Proof.
      intros ** Hxss Hyss Same n.
      apply same_clock_impl in Same.
      unfold Indexed.same_clock, Indexed.instant_same_clock in Same;
        specialize (Same n).
      split; intros Indexed.
      - destruct Same as [E|Ne].
        + rewrite tr_streams_app in E; apply Forall_app in E; tauto.
        + rewrite tr_streams_app in Ne; apply Forall_app in Ne as [NIndexed].
          induction xss; simpl in *; inv NIndexed; try now inv Indexed.
          now contradict Hxss.
      - destruct Same as [E|Ne].
        + rewrite tr_streams_app in E; apply Forall_app in E; tauto.
        + rewrite tr_streams_app in Ne; apply Forall_app in Ne as [? NIndexed].
          induction yss; simpl in *; inv NIndexed; try now inv Indexed.
          now contradict Hyss.
    Qed.

    Lemma const_index:
      forall n xs c b,
        xs ≡ CoInd.const c b ->
        tr_stream xs n = if tr_stream b n then present (sem_const c) else absent.
    Proof.
      induction n; intros ** E;
        unfold_Stv b; unfold_Stv xs; inv E; simpl in *; try discriminate;
          repeat rewrite tr_stream_0; repeat rewrite tr_stream_S; auto.
    Qed.

    Lemma when_index:
      forall n k xs cs rs,
        CoInd.when k xs cs rs ->
        (tr_stream xs n = absent
         /\ tr_stream cs n = absent
         /\ tr_stream rs n = absent)
        \/
        (exists x c,
            tr_stream xs n = present x
            /\ tr_stream cs n = present c
            /\ val_to_bool c = Some (negb k)
            /\ tr_stream rs n = absent)
        \/
        (exists x c,
            tr_stream xs n = present x
            /\ tr_stream cs n = present c
            /\ val_to_bool c = Some k
            /\ tr_stream rs n = present x).
    Proof.
      induction n; intros ** When.
      - inv When; repeat rewrite tr_stream_0; intuition.
        + right; left. do 2 eexists; intuition.
        + right; right. do 2 eexists; intuition.
      - inv When; repeat rewrite tr_stream_S; auto.
    Qed.

    Lemma lift1_index:
      forall n op t xs ys,
        CoInd.lift1 op t xs ys ->
        (tr_stream xs n = absent /\ tr_stream ys n = absent)
        \/
        (exists x y,
            tr_stream xs n = present x
            /\ sem_unop op x t = Some y
            /\ tr_stream ys n = present y).
    Proof.
      induction n; intros ** Lift1.
      - inv Lift1; repeat rewrite tr_stream_0; intuition.
        right. do 2 eexists; intuition; auto.
      - inv Lift1; repeat rewrite tr_stream_S; auto.
    Qed.

    Lemma lift2_index:
      forall n op t1 t2 xs ys zs,
        CoInd.lift2 op t1 t2 xs ys zs ->
        (tr_stream xs n = absent
         /\ tr_stream ys n = absent
         /\ tr_stream zs n = absent)
        \/
        (exists x y z,
            tr_stream xs n = present x
            /\ tr_stream ys n = present y
            /\ sem_binop op x t1 y t2 = Some z
            /\ tr_stream zs n = present z).
    Proof.
      induction n; intros ** Lift2.
      - inv Lift2; repeat rewrite tr_stream_0; intuition.
        right. do 3 eexists; intuition; auto.
      - inv Lift2; repeat rewrite tr_stream_S; auto.
    Qed.

    Hint Constructors Indexed.sem_clock_instant.
    Lemma sem_clock_index:
      forall n H b ck bs,
        CoInd.sem_clock H b ck bs ->
        (ck = Cbase
         /\ tr_stream b n = tr_stream bs n)
        \/
        (exists ck' x k c,
            ck = Con ck' x k
            /\ Indexed.sem_clock_instant (tr_stream b n) (Indexed.restr (tr_history H) n) ck' true
            /\ Indexed.sem_var_instant (Indexed.restr (tr_history H) n) x (present c)
            /\ val_to_bool c = Some k
            /\ tr_stream bs n = true)
        \/
        (exists ck' x k,
            ck = Con ck' x k
            /\ Indexed.sem_clock_instant (tr_stream b n) (Indexed.restr (tr_history H) n) ck' false
            /\ Indexed.sem_var_instant (Indexed.restr (tr_history H) n) x absent
            /\ tr_stream bs n = false)
        \/
        (exists ck' x k c,
            ck = Con ck' x (negb k)
            /\ Indexed.sem_clock_instant (tr_stream b n) (Indexed.restr (tr_history H) n) ck' true
            /\ Indexed.sem_var_instant (Indexed.restr (tr_history H) n) x (present c)
            /\ val_to_bool c = Some k
            /\ tr_stream bs n = false).
    Proof.
      Local Ltac rew_0 := try match goal with
                                H: tr_stream _ _ = _ |- _ => now rewrite tr_stream_0 in H
                              end.
      intros n H b ck; revert n H b; induction ck as [|ck ? x k].
      - inversion_clear 1 as [? ? ? Eb| | |].
        left; intuition.
        now rewrite Eb.
      - intro n; revert x k; induction n; intros x k H bk bk' Indexed.
        + inversion_clear Indexed as [|? ? ? ? ? ? ? ? ? IndexedCk Hvar
                                     |? ? ? ? ? ? ? ? IndexedCk Hvar
                                     |? ? ? ? ? ? ? ? ? IndexedCk Hvar].
          * right; left.
            apply sem_var_impl with (b:=tr_stream bk) in Hvar;
              unfold Indexed.sem_var, Indexed.lift in Hvar ; specialize (Hvar 0);
                rewrite tr_stream_0 in Hvar.
            do 4 eexists; intuition; eauto.
            apply (IHck 0) in IndexedCk as [(? & E)|[|[]]]; destruct_conjs;
              subst; eauto; rew_0.
            rewrite E, tr_stream_0; constructor.
          * right; right; left.
            apply sem_var_impl with (b:=tr_stream bk) in Hvar;
              unfold Indexed.sem_var, Indexed.lift in Hvar ; specialize (Hvar 0);
                rewrite tr_stream_0 in Hvar.
            do 3 eexists; intuition.
            apply (IHck 0) in IndexedCk as [(? & E)|[|[]]]; destruct_conjs;
              subst; eauto; rew_0.
            rewrite E, tr_stream_0; constructor.
          * right; right; right.
            apply sem_var_impl with (b:=tr_stream bk) in Hvar;
              unfold Indexed.sem_var, Indexed.lift in Hvar; specialize (Hvar 0);
                rewrite tr_stream_0 in Hvar.
            do 4 eexists; intuition; eauto.
            apply (IHck 0) in IndexedCk as [(? & E)|[|[]]]; destruct_conjs;
              subst; eauto; rew_0.
            rewrite E, tr_stream_0; constructor.
        + inversion_clear Indexed; rewrite <-tr_stream_tl, tr_history_tl; eauto.
    Qed.

    Corollary sem_clock_impl:
      forall n H b ck bs,
        CoInd.sem_clock H b ck bs ->
        Indexed.sem_clock_instant (tr_stream b n) (Indexed.restr (tr_history H) n) ck (tr_stream bs n).
    Proof.
      intros ** Indexed.
      apply (sem_clock_index n) in Indexed as [(Hck & E)
                                          |[(? & ? & ? & ? & Hck & ? & ? & ? & E)
                                           |[(? & ? & ? & Hck & ? & ? & E)
                                            |(? & ? & ? & ? & Hck & ? & ? & ? & E)]]];
        match goal with H: tr_stream _ _ = _ |- _ => rewrite H end;
        subst; eauto.
    Qed.

    Hint Constructors Indexed.sem_lexp_instant.
    Lemma sem_lexp_impl:
      forall H b e es,
        CoInd.sem_lexp H b e es ->
        Indexed.sem_lexp (tr_stream b) (tr_history H) e (tr_stream es).
    Proof.
      induction 1 as [? ? ? ? Hconst
                            |? ? ? ? ? Hvar
                            |? ? ? ? ? ? ? ? ? ? Hvar Hwhen
                            |? ? ? ? ? ? ? ? ? Hlift1
                            |? ? ? ? ? ? ? ? ? ? ? ? ? Hlift2]; intro n.
      - apply (const_index n) in Hconst; rewrite Hconst.
        destruct (tr_stream b n); eauto.
      - apply sem_var_impl with (b := tr_stream b) in Hvar; eauto.
      - specialize (IHsem_lexp n).
        apply sem_var_impl with (b := tr_stream b) in Hvar.
        unfold Indexed.sem_var, Indexed.lift in Hvar.
        specialize (Hvar n).
        apply (when_index n) in Hwhen
          as [(Hes & Hxs & Hos)
             |[(? & ? & Hes & Hxs & ? & Hos)
              |(? & ? & Hes & Hxs & ? & Hos)]];
          rewrite Hos; rewrite Hes in IHsem_lexp; rewrite Hxs in Hvar;
            eauto.
        rewrite <-(Bool.negb_involutive k).
        eapply Indexed.Swhen_abs1; eauto.
      - specialize (IHsem_lexp n).
        apply (lift1_index n) in Hlift1
          as [(Hes & Hos)|(? & ? & Hes & ? & Hos)];
          rewrite Hos; rewrite Hes in IHsem_lexp;
            econstructor; eauto.
      - specialize (IHsem_lexp1 n).
        specialize (IHsem_lexp2 n).
        apply (lift2_index n) in Hlift2
          as [(Hes1 & Hes2 & Hos)|(? & ? & ? & Hes1 & Hes2 & ? & Hos)];
          rewrite Hos; rewrite Hes1 in IHsem_lexp1; rewrite Hes2 in IHsem_lexp2;
            eauto.
    Qed.

    Lemma sem_laexp_index:
      forall n H b ck le es,
        CoInd.sem_laexp H b ck le es ->
        (Indexed.sem_clock_instant (tr_stream b n) (Indexed.restr (tr_history H) n) ck false
         /\ Indexed.sem_lexp_instant (tr_stream b n) (Indexed.restr (tr_history H) n) le absent
         /\ tr_stream es n = absent)
        \/
        (exists e,
            Indexed.sem_clock_instant (tr_stream b n) (Indexed.restr (tr_history H) n) ck true
            /\ Indexed.sem_lexp_instant (tr_stream b n) (Indexed.restr (tr_history H) n) le (present e)
            /\ tr_stream es n = present e).
    Proof.
      induction n; intros ** Indexed.
      - inversion_clear Indexed as [? ? ? ? ? ? ? Indexed' Hck|? ? ? ? ? ? Indexed' Hck];
          apply sem_lexp_impl in Indexed'; specialize (Indexed' 0);
            repeat rewrite tr_stream_0; repeat rewrite tr_stream_0 in Indexed';
              apply (sem_clock_impl 0) in Hck; rewrite tr_stream_0 in Hck.
        + right. eexists; intuition; auto.
        + left; intuition.
      - inversion_clear Indexed as [? ? ? ? ? ? ? Indexed'|? ? ? ? ? ? Indexed'];
          apply sem_lexp_impl in Indexed';
          rewrite tr_stream_S, tr_history_tl; eauto.
    Qed.

    Corollary sem_laexp_impl:
      forall H b e es ck,
        CoInd.sem_laexp H b ck e es ->
        Indexed.sem_laexp (tr_stream b) (tr_history H) ck e (tr_stream es).
    Proof.
      intros ** Indexed n.
      apply (sem_laexp_index n) in Indexed as [(? & ? & Hes)|(? & ? & ? & Hes)];
        rewrite Hes; auto using Indexed.sem_laexp_instant.
    Qed.

    Lemma sem_laexps_index:
      forall n H b ck les ess,
        CoInd.sem_laexps H b ck les ess ->
        (Indexed.sem_clock_instant (tr_stream b n) (Indexed.restr (tr_history H) n) ck false
         /\ Indexed.sem_lexps_instant (tr_stream b n) (Indexed.restr (tr_history H) n) les (tr_streams ess n)
         /\ tr_streams ess n = List.map (fun _ => absent) les)
        \/
        (Indexed.sem_clock_instant (tr_stream b n) (Indexed.restr (tr_history H) n) ck true
         /\ Indexed.sem_lexps_instant (tr_stream b n) (Indexed.restr (tr_history H) n) les (tr_streams ess n)
         /\ Forall (fun e => e <> absent) (tr_streams ess n)).
    Proof.
      induction n; intros ** Indexed.
      - inversion_clear Indexed as [? ? ? ? ? ? Indexed' Hess Hck|? ? ? ? ? ? Indexed' Hess Hck];
          apply (sem_clock_impl 0) in Hck; rewrite tr_stream_0 in Hck.
        + right. intuition; auto.
          *{ clear Hess. induction Indexed' as [|? ? ? ? Indexed]; simpl; constructor.
             - now apply sem_lexp_impl in Indexed.
             - eapply IHIndexed', CoInd.sem_laexps_cons; eauto.
           }
          * clear - Hess.
            induction ess; inv Hess; constructor; auto.
        + left. intuition; auto.
          *{ clear Hess. induction Indexed' as [|? ? ? ? Indexed]; simpl; constructor.
             - now apply sem_lexp_impl in Indexed.
             - eapply IHIndexed', CoInd.sem_laexps_cons; eauto.
           }
          * clear - Indexed' Hess.
            induction Indexed'; inv Hess; simpl; auto.
            f_equal; auto.
      - destruct b; inversion_clear Indexed as [? ? ? ? ? ? Indexed' Hess Hck|? ? ? ? ? ? Indexed' Hess Hck];
          rewrite tr_stream_S, tr_history_tl, <-tr_streams_tl; auto.
    Qed.

    Corollary sem_laexps_impl:
      forall H b ck es ess,
        CoInd.sem_laexps H b ck es ess ->
        Indexed.sem_laexps (tr_stream b) (tr_history H) ck es (tr_streams ess).
    Proof.
      intros ** Indexed n.
      apply (sem_laexps_index n) in Indexed as [(? & ? & Hes)|(? & ? & Hes)].
      - eright; eauto.
      - assert (exists vs, tr_streams ess n = List.map present vs) as (vs & ?).
        { clear - Hes.
          induction ess as [|es].
          - exists nil; auto.
          - simpl in *; inversion_clear Hes as [|? ? E].
            destruct (tr_stream es n) as [|v]; try now contradict E.
            apply IHess in H as (vs & ?).
            exists (v :: vs); simpl.
            f_equal; auto.
        }
        left with (cs := vs); eauto.
    Qed.

    Lemma merge_index:
      forall n xs ts fs rs,
        CoInd.merge xs ts fs rs ->
        (tr_stream xs n = absent
         /\ tr_stream ts n = absent
         /\ tr_stream fs n = absent
         /\ tr_stream rs n = absent)
        \/
        (exists t,
            tr_stream xs n = present true_val
            /\ tr_stream ts n = present t
            /\ tr_stream fs n = absent
            /\ tr_stream rs n = present t)
        \/
        (exists f,
            tr_stream xs n = present false_val
            /\ tr_stream ts n = absent
            /\ tr_stream fs n = present f
            /\ tr_stream rs n = present f).
    Proof.
      induction n; intros ** Merge.
      - inv Merge; repeat rewrite tr_stream_0; intuition.
        + right; left. eexists; intuition.
        + right; right. eexists; intuition.
      - inv Merge; repeat rewrite tr_stream_S; auto.
    Qed.

    Lemma ite_index:
      forall n xs ts fs rs,
        CoInd.ite xs ts fs rs ->
        (tr_stream xs n = absent
         /\ tr_stream ts n = absent
         /\ tr_stream fs n = absent
         /\ tr_stream rs n = absent)
        \/
        (exists t f,
            tr_stream xs n = present true_val
            /\ tr_stream ts n = present t
            /\ tr_stream fs n = present f
            /\ tr_stream rs n = present t)
        \/
        (exists t f,
            tr_stream xs n = present false_val
            /\ tr_stream ts n = present t
            /\ tr_stream fs n = present f
            /\ tr_stream rs n = present f).
    Proof.
      induction n; intros ** Ite.
      - inv Ite; repeat rewrite tr_stream_0; intuition.
        + right; left. do 2 eexists; now intuition.
        + right; right. do 2 eexists; now intuition.
      - inv Ite; repeat rewrite tr_stream_S; auto.
    Qed.

    Lemma sem_cexp_impl:
      forall H b e es,
        CoInd.sem_cexp H b e es ->
        Indexed.sem_cexp (tr_stream b) (tr_history H) e (tr_stream es).
    Proof.
      unfold Indexed.sem_caexp, Indexed.lift.
      induction 1 as [? ? ? ? ? ? ? ? ? Hvar Ht ? ? ? Hmerge
                    |? ? ? ? ? ? ? ? ? He Ht ? ? ? Hite
                    |? ? ? ? He]; intro n.
      - specialize (IHsem_cexp1 n).
        specialize (IHsem_cexp2 n).
        apply sem_var_impl with (b := tr_stream b) in Hvar; eauto.
        unfold Indexed.sem_var, Indexed.lift in Hvar.
        specialize (Hvar n).
        rename H0_ into Hf.
        apply (merge_index n) in Hmerge
          as [(Hxs & Hts & Hfs & Hos)
             |[(? & Hxs & Hts & Hfs & Hos)
              |(? & Hxs & Hts & Hfs & Hos)]];
          rewrite Hos; rewrite Hts in IHsem_cexp1; rewrite Hfs in IHsem_cexp2;
            rewrite Hxs in Hvar; try (now constructor; auto).
        apply Indexed.Smerge_false; auto.

      - specialize (IHsem_cexp1 n).
        specialize (IHsem_cexp2 n).
        eapply sem_lexp_impl in He.
        specialize (He n).
        apply (ite_index n) in Hite
          as [(Hes & Hts & Hfs & Hos)
             |[(ct & cf & Hes & Hts & Hfs & Hos)
              |(ct & cf & Hes & Hts & Hfs & Hos)]];
          rewrite Hos; rewrite Hts in IHsem_cexp1; rewrite Hfs in IHsem_cexp2;
            rewrite Hes in He.
        + constructor; auto.
        + change (present ct) with (if true then present ct else present cf).
          econstructor; eauto.
          apply val_to_bool_true.
        + change (present cf) with (if false then present ct else present cf).
          econstructor; eauto.
          apply val_to_bool_false.

      - apply sem_lexp_impl in He.
        specialize (He n).
        constructor; auto.
    Qed.

    Lemma sem_caexp_index:
      forall n H b ck le es,
        CoInd.sem_caexp H b ck le es ->
        (Indexed.sem_clock_instant (tr_stream b n) (Indexed.restr (tr_history H) n) ck false
         /\ Indexed.sem_cexp_instant (tr_stream b n) (Indexed.restr (tr_history H) n) le absent
         /\ tr_stream es n = absent)
        \/
        (exists e,
            Indexed.sem_clock_instant (tr_stream b n) (Indexed.restr (tr_history H) n) ck true
            /\ Indexed.sem_cexp_instant (tr_stream b n) (Indexed.restr (tr_history H) n) le (present e)
            /\ tr_stream es n = present e).
    Proof.
      induction n; intros ** Indexed.
      - inversion_clear Indexed as [? ? ? ? ? ? ? Indexed' Hck|? ? ? ? ? ? Indexed' Hck];
          apply sem_cexp_impl in Indexed'; specialize (Indexed' 0);
            repeat rewrite tr_stream_0; repeat rewrite tr_stream_0 in Indexed';
              apply (sem_clock_impl 0) in Hck; rewrite tr_stream_0 in Hck.
        + right. eexists; intuition; auto.
        + left; intuition.
      - inversion_clear Indexed as [? ? ? ? ? ? ? Indexed'|? ? ? ? ? ? Indexed'];
          apply sem_cexp_impl in Indexed';
          repeat rewrite tr_stream_S; rewrite tr_history_tl; eauto.
    Qed.

    Corollary sem_caexp_impl:
      forall H b e es ck,
        CoInd.sem_caexp H b ck e es ->
        Indexed.sem_caexp (tr_stream b) (tr_history H) ck e (tr_stream es).
    Proof.
      intros ** Indexed n.
      apply (sem_caexp_index n) in Indexed as [(? & ? & Hes)|(? & ? & ? & Hes)];
        rewrite Hes; now constructor.
    Qed.

    Lemma tr_stream_reset:
      forall n xs,
        tr_stream (CoInd.reset_of xs) n = Indexed.reset_of (tr_stream xs) n.
    Proof.
      induction n; intros.
      - unfold_Stv xs; unfold Indexed.reset_of;
          rewrite unfold_Stream at 1; simpl; rewrite tr_stream_0; auto.
      - unfold_Stv xs; unfold Indexed.reset_of;
          rewrite unfold_Stream at 1; simpl; auto;
            eapply IHn.
    Qed.

    Lemma fby_impl:
      forall n c xs,
      tr_stream (CoInd.fby c xs) n = fby c (tr_stream xs) n.
    Proof.
      induction n; intros.
      - unfold_Stv xs; rewrite unfold_Stream at 1;
          unfold fby; simpl; now rewrite tr_stream_0.
      - unfold_Stv xs; rewrite unfold_Stream at 1;
          unfold fby; simpl; repeat rewrite tr_stream_S;
            rewrite IHn; unfold fby;
              destruct (tr_stream xs n); auto; f_equal;
                clear IHn; induction n; simpl; auto;
                  rewrite tr_stream_S; destruct (tr_stream xs n); auto.
    Qed.

    Lemma sem_clock_tr_stream:
      forall xss,
        Indexed.clock_of (tr_streams xss) (tr_stream (CoInd.clocks_of xss)).
    Proof.
      split; intros ** H.
      - revert dependent xss; induction n; intros; induction xss as [|xs];
          rewrite unfold_Stream at 1; simpl in *;
          try rewrite tr_stream_0; try rewrite tr_stream_S; auto.
        + inversion_clear H as [|? ? ToMap Forall].
          apply andb_true_intro; split.
          * unfold_St xs; rewrite tr_stream_0 in ToMap.
            apply Bool.negb_true_iff; rewrite not_equiv_decb_equiv; intro E.
            contradiction.
          * apply IHxss in Forall.
            clear - Forall; induction xss as [|xs]; simpl; auto.
        + inversion_clear H.
          apply IHn. constructor.
          * now rewrite tr_stream_tl.
          * fold (@tr_streams value).
            now rewrite tr_streams_tl.
      - revert dependent xss; induction n; intros; induction xss as [|xs];
          simpl in *; constructor.
        + rewrite unfold_Stream in H at 1; simpl in H;
            rewrite tr_stream_0 in H; apply andb_prop in H as [].
          unfold_St xs; rewrite tr_stream_0; simpl in *.
          intro; subst; discriminate.
        + apply IHxss.
          rewrite unfold_Stream in H at 1; simpl in H;
            rewrite tr_stream_0 in H; apply andb_prop in H as [? Forall].
          clear - Forall; induction xss; rewrite unfold_Stream at 1; simpl;
            now rewrite tr_stream_0.
        + rewrite unfold_Stream in H at 1; simpl in H; rewrite tr_stream_S in H.
          apply IHn in H; inv H.
          now rewrite <-tr_stream_tl.
        + rewrite unfold_Stream in H at 1; simpl in H; rewrite tr_stream_S in H.
          apply IHn in H; inv H.
          now rewrite <-tr_streams_tl.
    Qed.

    Remark count_true_not_0:
      forall r n,
        count (tr_stream (true ::: r)) n <> 0.
    Proof.
      intros; induction n; simpl.
      - omega.
      - rewrite tr_stream_S.
        destruct (tr_stream r n); auto.
    Qed.

    Remark count_true_not_0':
      forall n r,
        tr_stream r n = true ->
        count (tr_stream r) n <> 0.
    Proof.
      induction n; simpl; intros r E; try rewrite E; auto.
    Qed.

    Remark tr_stream_mask_true_0:
      forall n r xs,
      tr_stream r n = true ->
      tr_stream (CoInd.mask absent 0 r xs) n = absent.
    Proof.
      induction n; intros ** E; rewrite unfold_Stream at 1; simpl;
        unfold_Stv r; unfold_Stv xs; auto; try rewrite tr_stream_S.
      - rewrite tr_stream_0 in E; discriminate.
      - pose proof (tr_stream_const absent); auto.
      - pose proof (tr_stream_const absent); auto.
      - apply IHn.
        rewrite tr_stream_S in E; auto.
      - apply IHn.
        rewrite tr_stream_S in E; auto.
    Qed.

    Lemma count_true_shift:
      forall n r,
        count (tr_stream (true ::: r)) n
        = if tr_stream r n then count (tr_stream r) n else S (count (tr_stream r) n).
    Proof.
      induction n; simpl; intros.
      - destruct (tr_stream r 0); auto.
      - specialize (IHn r).
        rewrite tr_stream_S.
        destruct (tr_stream r n) eqn: E';
          destruct (tr_stream r (S n)); rewrite IHn; auto.
    Qed.

    Lemma count_false_shift:
      forall n r,
        count (tr_stream (false ::: r)) n
        = if tr_stream r n then count (tr_stream r) n - 1 else count (tr_stream r) n.
    Proof.
      induction n; simpl; intros.
      - destruct (tr_stream r 0); auto.
      - specialize (IHn r).
        rewrite tr_stream_S.
        destruct (tr_stream r n) eqn: E';
          destruct (tr_stream r (S n)); rewrite IHn; try omega.
        + apply Minus.minus_Sn_m, count_true_ge_1; auto.
        + rewrite Minus.minus_Sn_m; try omega.
          apply count_true_ge_1; auto.
    Qed.

    Lemma tr_stream_mask_false_true:
      forall n r xs k k',
        tr_stream r n = false ->
        count (tr_stream (true ::: r)) n = S k ->
        tr_stream (CoInd.mask absent k' r xs) n
        = if EqNat.beq_nat k k' then tr_stream xs n else absent.
    Proof.
      intros ** E C.
      rewrite count_true_shift, E in C; injection C; clear C; intro C.
      revert k' k r xs E C; induction n; simpl; intros.
      - rewrite E in C.
         destruct (EqNat.beq_nat k k') eqn: E'.
        + apply EqNat.beq_nat_true in E'; subst.
          unfold_Stv r; unfold_St xs; rewrite unfold_Stream at 1;
            simpl; rewrite <-E'; repeat rewrite tr_stream_0; auto.
          rewrite tr_stream_0 in E; discriminate.
        + apply EqNat.beq_nat_false in E'.
          unfold_Stv r; unfold_St xs; rewrite unfold_Stream at 1;
            destruct k' as [|[]]; simpl; try (exfalso; now apply E').
          * pose proof (tr_stream_const absent); auto.
          * apply tr_stream_0.
      - destruct (EqNat.beq_nat k k') eqn: E'.
        + apply EqNat.beq_nat_true in E'; subst.
          unfold_Stv r; unfold_St xs; rewrite unfold_Stream at 1;
            destruct k' as [|[]]; simpl; repeat rewrite tr_stream_S; rewrite E in E';
              try discriminate; rewrite tr_stream_S in E.
          * inv E'; exfalso; eapply count_true_not_0; eauto.
          * erewrite IHn; eauto.
            rewrite count_true_shift, E in E'; injection E'; clear E'; intro E'.
            rewrite E', <-plus_n_O, <-EqNat.beq_nat_refl; auto.
          * rewrite count_true_shift, E in E'. inv E'.
            erewrite IHn; auto.
            rewrite <-plus_n_O, <-EqNat.beq_nat_refl; auto.
          * rewrite count_false_shift, E in E'.
            erewrite IHn; eauto; auto.
          * rewrite count_false_shift, E in E'.
            erewrite IHn; eauto; auto.
          * rewrite count_false_shift, E in E'.
            erewrite IHn, <-EqNat.beq_nat_refl; auto.
        + apply EqNat.beq_nat_false in E'.
          unfold_Stv r; unfold_St xs; rewrite unfold_Stream at 1;
            destruct k' as [|[]]; simpl; rewrite E in C; subst;
              repeat rewrite tr_stream_S; rewrite tr_stream_S in E;
                try (exfalso; now apply E').
          * pose proof (tr_stream_const absent); auto.
          * erewrite IHn; eauto.
            rewrite count_true_shift, E, NPeano.Nat.succ_inj_wd_neg,
            <-EqNat.beq_nat_false_iff in E'.
            rewrite <-plus_n_O, E'; auto.
          * erewrite IHn; eauto.
            rewrite count_true_shift, E, NPeano.Nat.succ_inj_wd_neg,
            <-EqNat.beq_nat_false_iff in E'.
            rewrite <-plus_n_O, E'; auto.
          * erewrite IHn; eauto.
            rewrite count_false_shift, E, <-EqNat.beq_nat_false_iff in E'.
            rewrite <-plus_n_O, E'; auto.
          * erewrite IHn; eauto.
            rewrite count_false_shift, E, <-EqNat.beq_nat_false_iff in E'.
            rewrite <-plus_n_O, E'; auto.
          * erewrite IHn; eauto.
            rewrite count_false_shift, E, <-EqNat.beq_nat_false_iff in E'.
            rewrite <-plus_n_O, E'; auto.
    Qed.

    Lemma tr_stream_mask_true_false:
      forall n r xs k k',
        tr_stream r n = true ->
        count (tr_stream (false ::: r)) n = k ->
        tr_stream (CoInd.mask absent (S k') r xs) n
        = if EqNat.beq_nat k k' then tr_stream xs n else absent.
    Proof.
      intros ** E C.
      rewrite count_false_shift, E in C.
      revert k' k r xs E C; induction n; simpl; intros.
      - rewrite E in C.
        destruct (EqNat.beq_nat k k') eqn: E'.
        + apply EqNat.beq_nat_true in E'; subst.
          unfold_Stv r; unfold_St xs; rewrite unfold_Stream at 1;
            simpl; rewrite <-E'; repeat rewrite tr_stream_0; auto.
          rewrite tr_stream_0 in E; discriminate.
        + apply EqNat.beq_nat_false in E'.
          unfold_Stv r; unfold_St xs; rewrite unfold_Stream at 1;
            destruct k' as [|[]]; simpl; try (exfalso; now apply E').
          * pose proof (tr_stream_const absent); auto.
          * apply tr_stream_0.
      - destruct (EqNat.beq_nat k k') eqn: E'.
        + apply EqNat.beq_nat_true in E'; subst.
          unfold_Stv r; unfold_St xs; rewrite unfold_Stream at 1;
            destruct k' as [|[]]; simpl; repeat rewrite tr_stream_S; rewrite E in E';
              try discriminate; rewrite tr_stream_S in E; simpl in E';
                try rewrite <-Minus.minus_n_O in E'.
          * exfalso; eapply count_true_not_0; eauto.
          * erewrite IHn; eauto.
            rewrite count_true_shift, E in E'.
            rewrite E', <-plus_n_O, <-EqNat.beq_nat_refl; auto.
          * rewrite count_true_shift, E in E'.
            erewrite IHn; auto.
            rewrite E'; simpl; rewrite <-plus_n_O, <-EqNat.beq_nat_refl; auto.
          * rewrite count_false_shift, E in E'.
            erewrite IHn; eauto; auto.
          * rewrite count_false_shift, E in E'.
            erewrite IHn; eauto; auto.
          * rewrite count_false_shift, E in E'.
            erewrite IHn, <-EqNat.beq_nat_refl; auto.
        + apply EqNat.beq_nat_false in E'.
          unfold_Stv r; unfold_St xs; rewrite unfold_Stream at 1;
            destruct k' as [|[]]; simpl; rewrite E in C; subst;
              repeat rewrite tr_stream_S; rewrite tr_stream_S in E;
                simpl in E'; try rewrite <-Minus.minus_n_O in E';
                try (exfalso; now apply E').
          * apply tr_stream_mask_true_0; auto.
          * erewrite IHn; eauto.
            rewrite count_true_shift, E in E'.
            rewrite <-plus_n_O.
            apply count_true_not_0' in E.
            destruct (count (tr_stream r) n) as [|[]];
              try (exfalso; now apply E); try (exfalso; now apply E').
            auto.
          * erewrite IHn; eauto.
            rewrite count_true_shift, E in E'.
            apply count_true_not_0' in E.
            destruct (count (tr_stream r) n) as [|[|]];
              try (exfalso; now apply E); simpl; auto.
            rewrite 2 NPeano.Nat.succ_inj_wd_neg, <-EqNat.beq_nat_false_iff in E'.
            rewrite <-plus_n_O, E'; auto.
          * erewrite IHn; eauto.
            rewrite count_false_shift, E, <-EqNat.beq_nat_false_iff in E'.
            rewrite <-plus_n_O, E'; auto.
          * erewrite IHn; eauto.
            rewrite count_false_shift, E, <-EqNat.beq_nat_false_iff in E'.
            rewrite <-plus_n_O, E'; auto.
          * erewrite IHn; eauto.
            rewrite count_false_shift, E, <-EqNat.beq_nat_false_iff in E'.
            rewrite <-plus_n_O, E'; auto.
    Qed.

    Lemma tr_stream_mask_same:
      forall n b r xs k k',
        tr_stream r n = b ->
        count (tr_stream (b ::: r)) n = k ->
        tr_stream (CoInd.mask absent k' r xs) n
        = if EqNat.beq_nat k k' then tr_stream xs n else absent.
    Proof.
      intros ** E C.
      destruct b.
      - rewrite count_true_shift, E in C.
        revert k' k r xs E C; induction n; simpl; intros.
        + rewrite E in C.
          destruct (EqNat.beq_nat k k') eqn: E'.
          * apply EqNat.beq_nat_true in E'; subst.
            unfold_Stv r; unfold_St xs; rewrite unfold_Stream at 1;
              simpl; rewrite <-E'; repeat rewrite tr_stream_0; auto.
            rewrite tr_stream_0 in E; discriminate.
          *{ apply EqNat.beq_nat_false in E'.
             unfold_Stv r; unfold_St xs; rewrite unfold_Stream at 1;
               destruct k' as [|[]]; simpl; try (exfalso; now apply E').
             - pose proof (tr_stream_const absent); auto.
             - apply tr_stream_0.
           }
        + destruct (EqNat.beq_nat k k') eqn: E'.
          *{ apply EqNat.beq_nat_true in E'; subst.
             unfold_Stv r; unfold_St xs; rewrite unfold_Stream at 1;
               destruct k' as [|[]]; simpl; repeat rewrite tr_stream_S; rewrite E in E';
                 try discriminate; rewrite tr_stream_S in E.
             - inv E'; exfalso; eapply count_true_not_0; eauto.
             - erewrite IHn; eauto.
               inv E';
                 rewrite count_true_shift, E, <-plus_n_O,
                 <-EqNat.beq_nat_refl; auto.
             - injection E'; clear E'; intro E'.
               rewrite count_false_shift in E'; rewrite E in E'.
               apply NPeano.Nat.sub_0_le in E'.
               pose proof (count_true_ge_1 _ _ E).
               apply Le.le_antisym in E'; auto.
               erewrite IHn; auto.
               rewrite E', <-plus_n_O, <-EqNat.beq_nat_refl; auto.
             - injection E'; clear E'; intro E'.
               erewrite IHn; eauto.
               inv E'; rewrite count_false_shift, E.
               pose proof (count_true_ge_1 _ _ E).
               rewrite Minus.minus_Sn_m; auto.
               simpl; rewrite <-Minus.minus_n_O, <-plus_n_O,
                      <-EqNat.beq_nat_refl; auto.
           }
          *{ apply EqNat.beq_nat_false in E'.
             unfold_Stv r; unfold_St xs; rewrite unfold_Stream at 1;
               destruct k' as [|[]]; simpl; rewrite E in C; subst;
                 repeat rewrite tr_stream_S; rewrite tr_stream_S in E;
                   try (exfalso; now apply E').
             - pose proof (tr_stream_const absent); auto.
             - erewrite IHn; eauto.
               rewrite count_true_shift, E, NPeano.Nat.succ_inj_wd_neg,
               <-EqNat.beq_nat_false_iff in E'.
               rewrite <-plus_n_O, E'; auto.
             - erewrite IHn; eauto.
               rewrite count_true_shift, E, NPeano.Nat.succ_inj_wd_neg,
               <-EqNat.beq_nat_false_iff in E'.
               rewrite <-plus_n_O, E'; auto.
             - erewrite IHn; eauto.
               pose proof (count_true_ge_1 _ _ E).
               rewrite count_false_shift, E, Minus.minus_Sn_m in E';
                 auto; simpl in E';
                   rewrite <-Minus.minus_n_O, <-EqNat.beq_nat_false_iff in E'.
               rewrite <-plus_n_O, E'; auto.
             - erewrite IHn; eauto.
               pose proof (count_true_ge_1 _ _ E).
               rewrite count_false_shift, E, Minus.minus_Sn_m in E';
                 auto; simpl in E';
                   rewrite <-Minus.minus_n_O, <-EqNat.beq_nat_false_iff in E'.
               rewrite <-plus_n_O, E'; auto.
             - erewrite IHn; eauto.
               pose proof (count_true_ge_1 _ _ E).
               rewrite count_false_shift, E, Minus.minus_Sn_m in E';
                 auto; simpl in E';
                   rewrite <-Minus.minus_n_O, <-EqNat.beq_nat_false_iff in E'.
               rewrite <-plus_n_O, E'; auto.
           }

      - rewrite count_false_shift, E in C.
        revert k' k r xs E C; induction n; simpl; intros.
        + rewrite E in C.
          destruct (EqNat.beq_nat k k') eqn: E'.
          * apply EqNat.beq_nat_true in E'; subst.
            unfold_Stv r; unfold_St xs; rewrite unfold_Stream at 1;
              simpl; rewrite <-E'; repeat rewrite tr_stream_0; auto.
            rewrite tr_stream_0 in E; discriminate.
          *{ apply EqNat.beq_nat_false in E'.
             unfold_Stv r; unfold_St xs; rewrite unfold_Stream at 1;
               destruct k' as [|[]]; simpl; try (exfalso; now apply E').
             - pose proof (tr_stream_const absent); auto.
             - apply tr_stream_0.
           }
        + destruct (EqNat.beq_nat k k') eqn: E'.
          *{ apply EqNat.beq_nat_true in E'; subst.
             unfold_Stv r; unfold_St xs; rewrite unfold_Stream at 1;
               destruct k' as [|[]]; simpl; repeat rewrite tr_stream_S; rewrite E in E';
                 try discriminate; rewrite tr_stream_S in E.
             - inv E'; exfalso; eapply count_true_not_0; eauto.
             - erewrite tr_stream_mask_false_true; eauto;
                 rewrite <-EqNat.beq_nat_refl; auto.
             - erewrite tr_stream_mask_false_true; eauto;
                 rewrite <-EqNat.beq_nat_refl; auto.
             - erewrite IHn; eauto.
               rewrite count_false_shift, E in E'.
               rewrite <-plus_n_O, E'; auto.
             - erewrite IHn; eauto.
               rewrite count_false_shift, E in E'.
               rewrite <-plus_n_O, E'; auto.
             - erewrite IHn; eauto.
               rewrite count_false_shift, E in E'.
               rewrite <-plus_n_O, E', <-EqNat.beq_nat_refl; auto.
           }
          *{ apply EqNat.beq_nat_false in E'.
             unfold_Stv r; unfold_St xs; rewrite unfold_Stream at 1;
               destruct k' as [|[]]; simpl; rewrite E in C; subst;
                 repeat rewrite tr_stream_S; rewrite tr_stream_S in E;
                   try (exfalso; now apply E').
             - pose proof (tr_stream_const absent); auto.
             - erewrite IHn; eauto.
               rewrite count_true_shift, E, NPeano.Nat.succ_inj_wd_neg,
               <-EqNat.beq_nat_false_iff in E'.
               rewrite <-plus_n_O, E'; auto.
             - erewrite IHn; eauto.
               rewrite count_true_shift, E, NPeano.Nat.succ_inj_wd_neg,
               <-EqNat.beq_nat_false_iff in E'.
               rewrite <-plus_n_O, E'; auto.
             - erewrite IHn; eauto.
               rewrite count_false_shift, E, <-EqNat.beq_nat_false_iff in E'.
               rewrite <-plus_n_O, E'; auto.
             - erewrite IHn; eauto.
               rewrite count_false_shift, E, <-EqNat.beq_nat_false_iff in E'.
               rewrite <-plus_n_O, E'; auto.
             - erewrite IHn; eauto.
               rewrite count_false_shift, E, <-EqNat.beq_nat_false_iff in E'.
               rewrite <-plus_n_O, E'; auto.
           }
    Qed.

    Ltac auto_f_equal H :=
      f_equal;
      [ idtac |
        erewrite H; eauto; unfold mask; simpl; rewrite tr_stream_S;
        repeat match goal with
               | H: tr_stream _ _ = _ |- _ => rewrite H
               | H: count ?x _ = _ |- _ => rewrite H
               | H:  EqNat.beq_nat _ _ = _ |- _ => rewrite H
               end; auto].

    Lemma mask_impl:
      forall k r xss n,
         tr_streams (List.map (CoInd.mask_v k r) xss) n
        = mask (Indexed.all_absent xss) k (tr_stream r) (tr_streams xss) n.
    Proof.
      induction xss as [|xs];
        simpl; intros.
      - unfold mask.
        destruct (EqNat.beq_nat k (count (tr_stream r) n)); auto.
      - induction n.
        + unfold_St xs; unfold_Stv r; unfold CoInd.mask_v, mask;
            rewrite unfold_Stream at 1; simpl;
            destruct k as [|[]]; simpl; f_equal;
              erewrite IHxss; eauto; unfold mask; auto.
        + unfold_St xs; unfold_Stv r; unfold CoInd.mask_v, mask.
          *{ rewrite unfold_Stream at 1; simpl.
             destruct k as [|[]]; simpl.
             - repeat rewrite tr_stream_S.
               destruct (tr_stream r n) eqn: E.
               + auto_f_equal IHxss.
                 pose proof (tr_stream_const absent); auto.
               + destruct (count (tr_stream (true ::: r)) n) eqn: E'.
                 * exfalso; eapply count_true_not_0; eauto.
                 * auto_f_equal IHxss.
                   pose proof (tr_stream_const absent); auto.
             - repeat rewrite tr_stream_S.
               destruct (tr_stream r n) eqn: E.
               + destruct (count (tr_stream (true ::: r)) n) eqn: E'.
                 * exfalso; eapply count_true_not_0; eauto.
                 * auto_f_equal IHxss.
                   apply tr_stream_mask_true_0; auto.
               + destruct (count (tr_stream (true ::: r)) n) as [|[]] eqn: E'.
                 * exfalso; eapply count_true_not_0; eauto.
                 * auto_f_equal IHxss.
                   erewrite tr_stream_mask_false_true; eauto; auto.
                 * auto_f_equal IHxss.
                   erewrite tr_stream_mask_false_true; eauto; auto.
             - repeat rewrite tr_stream_S.
               destruct (tr_stream r n) eqn: E.
               + destruct (count (tr_stream (true ::: r)) n) eqn: E'.
                 * exfalso; eapply count_true_not_0; eauto.
                 *{ destruct (EqNat.beq_nat n0 n1) eqn: E''; auto_f_equal IHxss.
                    - erewrite tr_stream_mask_same; eauto.
                      apply EqNat.beq_nat_true, eq_S, EqNat.beq_nat_true_iff in E'';
                        rewrite NPeano.Nat.eqb_sym, E''; auto.
                    - erewrite tr_stream_mask_same; eauto.
                      apply EqNat.beq_nat_false, not_eq_S, EqNat.beq_nat_false_iff in E'';
                        rewrite NPeano.Nat.eqb_sym, E''; auto.
                  }
               + destruct (count (tr_stream (true ::: r)) n) as [|[]] eqn: E'.
                 * exfalso; eapply count_true_not_0; eauto.
                 * auto_f_equal IHxss.
                   erewrite tr_stream_mask_false_true; eauto; auto.
                 *{ destruct (EqNat.beq_nat n0 n1) eqn: E''; auto_f_equal IHxss.
                    - erewrite tr_stream_mask_false_true; eauto.
                      apply EqNat.beq_nat_true, eq_S, EqNat.beq_nat_true_iff in E'';
                        rewrite NPeano.Nat.eqb_sym, E''; auto.
                    - erewrite tr_stream_mask_false_true; eauto.
                      apply EqNat.beq_nat_false, not_eq_S, EqNat.beq_nat_false_iff in E'';
                        rewrite NPeano.Nat.eqb_sym, E''; auto.
                  }
           }

          *{ rewrite unfold_Stream at 1; simpl.
             destruct k as [|[]]; simpl.
             - repeat rewrite tr_stream_S.
               destruct (tr_stream r n) eqn: E.
               + auto_f_equal IHxss.
                 apply tr_stream_mask_true_0; auto.
               + destruct (count (tr_stream (false ::: r)) n) eqn: E';
                   auto_f_equal IHxss; erewrite tr_stream_mask_same; eauto; auto.
             - repeat rewrite tr_stream_S.
               destruct (tr_stream r n) eqn: E.
               + destruct (count (tr_stream (false ::: r)) n) eqn: E';
                   auto_f_equal IHxss;
                   erewrite tr_stream_mask_true_false; eauto; auto.
               + destruct (count (tr_stream (false ::: r)) n) as [|[]] eqn: E';
                   auto_f_equal IHxss; erewrite tr_stream_mask_same; eauto; auto.
             - repeat rewrite tr_stream_S.
               destruct (tr_stream r n) eqn: E.
               + destruct (count (tr_stream (false ::: r)) n) eqn: E'.
                 * auto_f_equal IHxss.
                   erewrite tr_stream_mask_true_false; eauto; auto.
                 *{ destruct (EqNat.beq_nat n0 n1) eqn: E''; auto_f_equal IHxss.
                    - erewrite tr_stream_mask_true_false; eauto.
                      apply EqNat.beq_nat_true, eq_S,
                      EqNat.beq_nat_true_iff in E'';
                        rewrite NPeano.Nat.eqb_sym, E''; auto.
                    - erewrite tr_stream_mask_true_false; eauto.
                      apply EqNat.beq_nat_false, not_eq_S,
                      EqNat.beq_nat_false_iff in E'';
                        rewrite NPeano.Nat.eqb_sym, E''; auto.
                  }
               + destruct (count (tr_stream (false ::: r)) n) as [|[]] eqn: E'.
                 * auto_f_equal IHxss.
                   erewrite tr_stream_mask_same; eauto; auto.
                 * auto_f_equal IHxss.
                   erewrite tr_stream_mask_same; eauto; auto.
                 *{ destruct (EqNat.beq_nat n0 n1) eqn: E''; auto_f_equal IHxss.
                    - erewrite tr_stream_mask_same; eauto.
                      apply EqNat.beq_nat_true, eq_S, eq_S,
                      EqNat.beq_nat_true_iff in E'';
                        rewrite NPeano.Nat.eqb_sym, E''; auto.
                    - erewrite tr_stream_mask_same; eauto.
                      apply EqNat.beq_nat_false, not_eq_S, not_eq_S,
                      EqNat.beq_nat_false_iff in E'';
                        rewrite NPeano.Nat.eqb_sym, E''; auto.
                  }
           }
    Qed.

    Remark all_absent_tr_streams:
      forall A n (xss: list (Stream A)),
        Indexed.all_absent (tr_streams xss n) = Indexed.all_absent xss.
    Proof.
      induction xss; simpl; auto; now f_equal.
    Qed.

    Theorem implies:
      (forall H b e,
          CoInd.sem_equation G H b e ->
          Indexed.sem_equation G (tr_stream b) (tr_history H) e)
      /\
      (forall f xss oss,
          CoInd.sem_node G f xss oss ->
          Indexed.sem_node G f (tr_streams xss) (tr_streams oss))
      /\
      (forall f r xss oss,
          CoInd.sem_reset G f r xss oss ->
          Indexed.sem_reset G f (tr_stream r) (tr_streams xss) (tr_streams oss)).
    Proof.
      apply CoInd.sem_equation_node_ind.
      - econstructor.
        + apply sem_var_impl; eauto.
        + apply sem_caexp_impl; auto.
      - econstructor; eauto.
        + apply sem_laexps_impl; auto.
        + apply sem_vars_impl; auto.
      - econstructor; auto.
        + apply sem_laexps_impl; eauto.
        + apply sem_vars_impl; eauto.
        + apply sem_var_impl; eauto.
        + eapply Indexed.sem_reset_compat.
          * intro; apply tr_stream_reset.
          * eauto.
      - econstructor; auto; subst.
        + apply sem_laexp_impl; eauto.
        + unfold Indexed.sem_var, Indexed.lift; intro.
          rewrite <-fby_impl.
          apply sem_var_impl; auto.
          exact (tr_stream b).
      - intros ** IHNode.
        constructor; intro.
        specialize (IHNode n).
        pose proof (mask_impl n r xss) as Hxss.
        pose proof (mask_impl n r yss) as Hyss.
        rewrite 2 all_absent_tr_streams.
        eapply Indexed.sem_node_compat; eauto.
      - intros ** Hin Hout Same ? ?. econstructor; eauto.
        + apply sem_clock_tr_stream.
        + apply sem_vars_impl; eauto.
        + apply sem_vars_impl; eauto.
        + now apply CoInd.same_clock_app_l, same_clock_impl in Same.
        + now apply CoInd.same_clock_app_r, same_clock_impl in Same.
        + apply same_clock_app_impl; auto.
          * intro; subst.
            apply Forall2_length in Hin; simpl in *.
            unfold CoInd.idents in Hin; rewrite map_length in Hin.
            pose proof n.(n_ingt0) as Nin.
            rewrite Hin in Nin; contradict Nin; apply Lt.lt_irrefl.
          * intro; subst.
            apply Forall2_length in Hout; simpl in *.
            unfold CoInd.idents in Hout; rewrite map_length in Hout.
            pose proof n.(n_outgt0) as Nout.
            rewrite Hout in Nout; contradict Nout; apply Lt.lt_irrefl.
    Qed.

    Definition equation_impl := proj1 implies.
    Definition node_impl := proj1 (proj2 implies).
    Definition reset_impl := proj2 (proj2 implies).

  End Global.

End COINDTONATMAP.
