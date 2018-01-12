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
       (Sem          : NLSEMANTICS Ids Op OpAux Clks Syn Str Ord)
       (Mod          : NLSEMANTICSCOIND Ids Op OpAux Clks Syn Ord).

  Section Global.

    Variable G : global.

    Definition to_map {A} (xs: Stream A) : stream A :=
      fun n => Str_nth n xs.

    Lemma to_map_0:
      forall {A} (xs: Stream A) x,
        to_map (x ::: xs) 0 = x.
    Proof.
      intros.
      unfold to_map, Str_nth; reflexivity.
    Qed.

    Lemma to_map_S:
      forall {A} (xs: Stream A) x n,
        to_map (x ::: xs) (S n) = to_map xs n.
    Proof.
      intros.
      unfold to_map, Str_nth; reflexivity.
    Qed.

    Add Parametric Morphism A : (@to_map A)
        with signature @EqSt A ==> eq ==> eq
          as to_map_morph.
    Proof.
      intros xs ys Exs n.
      revert xs ys Exs; induction n; intros; destruct xs, ys; inv Exs.
      - rewrite 2 to_map_0; auto.
      - rewrite 2 to_map_S; auto.
    Qed.

    Lemma to_map_const:
      forall {A} (c: A) n,
        to_map (Streams.const c) n = c.
    Proof.
      induction n; rewrite unfold_Stream at 1; simpl.
      - now rewrite to_map_0.
      - now rewrite to_map_S.
    Qed.

    Lemma to_map_tl:
      forall {A} (xs: Stream A) n,
        to_map (tl xs) n = to_map xs (S n).
    Proof.
      induction n; unfold_St xs; simpl;
        now rewrite to_map_S.
    Qed.

    (** explain all this weirdness *)
    Fixpoint to_maps {A} (xss: list (Stream A)) : stream (list A) :=
      match xss with
      | [] => fun n => []
      | xs :: xss => fun n => to_map xs n :: to_maps xss n
      end.

    Fact to_maps_app:
      forall A (xss yss: list (Stream A)) n,
        to_maps (xss ++ yss) n = to_maps xss n ++ to_maps yss n.
    Proof.
      intros; induction xss; simpl; auto.
      f_equal; auto.
    Qed.

    Lemma to_maps_tl:
      forall xss n,
        to_maps (List.map (tl (A:=value)) xss) n = to_maps xss (S n).
    Proof.
      intros; induction xss; simpl; auto.
      f_equal; auto.
    Qed.

    Definition hist_to_map (H: Mod.history) : Sem.history :=
      PM.map to_map H.

    Lemma option_map_map:
      forall {A B C} (f: A -> B) (g: B -> C) o,
        option_map g (option_map f o) = option_map (fun x => g (f x)) o.
    Proof.
      destruct o; simpl; auto.
    Qed.

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

    Lemma hist_to_map_tl:
      forall n H,
        Sem.restr (hist_to_map H) (S n) = Sem.restr (hist_to_map (Mod.history_tl H)) n.
    Proof.
      unfold Sem.restr, Mod.history_tl, hist_to_map.
      intros.
      repeat rewrite pm_map_map.
      (** WTF !?!??! *)
      reflexivity.
    Qed.

    Lemma sem_var_impl:
      forall H b x xs,
      Mod.sem_var H x xs ->
      Sem.sem_var b (hist_to_map H) x (to_map xs).
    Proof.
      intros ** Find n.
      constructor.
      inv Find.
      unfold Sem.restr, hist_to_map.
      unfold PM.map.
      rewrite 2 PM.gmapi.
      erewrite PM.find_1; eauto; simpl.
      f_equal.
      apply eqst_ntheq; symmetry; auto.
    Qed.

    Corollary sem_vars_impl:
      forall H b xs xss,
      Forall2 (Mod.sem_var H) xs xss ->
      Sem.sem_vars b (hist_to_map H) xs (to_maps xss).
    Proof.
      induction 1 as [|? ? ? ? Find];
        simpl; unfold Sem.sem_vars, Sem.lift; auto.
      intro; constructor; auto.
      apply sem_var_impl; auto.
    Qed.

    Lemma same_clock_impl:
      forall xss,
        Mod.same_clock xss ->
        Sem.same_clock (to_maps xss).
    Proof.
      unfold Sem.same_clock, Sem.instant_same_clock.
      intros.
      destruct (H n) as [E|Ne].
      - left; induction xss; simpl; constructor; inv E; auto.
        apply IHxss; auto.
        eapply Mod.same_clock_cons; eauto.
      - right; induction xss; simpl; constructor; inv Ne; auto.
        apply IHxss; eauto using Mod.same_clock_cons.
    Qed.

    Lemma same_clock_app_impl:
      forall xss yss,
        xss <> [] ->
        yss <> [] ->
        Mod.same_clock (xss ++ yss) ->
        forall n, Sem.absent_list (to_maps xss n) <-> Sem.absent_list (to_maps yss n).
    Proof.
      intros ** Hxss Hyss Same n.
      apply same_clock_impl in Same.
      unfold Sem.same_clock, Sem.instant_same_clock in Same;
        specialize (Same n).
      split; intros Sem.
      - destruct Same as [E|Ne].
        + rewrite to_maps_app in E; apply Forall_app in E; tauto.
        + rewrite to_maps_app in Ne; apply Forall_app in Ne as [NSem].
          induction xss; simpl in *; inv NSem; inv Sem.
          * exfalso; now apply Hxss.
          * contradiction.
      - destruct Same as [E|Ne].
        + rewrite to_maps_app in E; apply Forall_app in E; tauto.
        + rewrite to_maps_app in Ne; apply Forall_app in Ne as [? NSem].
          induction yss; simpl in *; inv NSem; inv Sem.
          * exfalso; now apply Hyss.
          * contradiction.
    Qed.

    Lemma const_index:
      forall n xs c b,
        xs ≡ Mod.const c b ->
        to_map xs n = if to_map b n then present (sem_const c) else absent.
    Proof.
      induction n; intros ** E;
        unfold_Stv b; unfold_Stv xs; inv E; simpl in *; try discriminate;
          repeat rewrite to_map_0; repeat rewrite to_map_S; auto.
    Qed.

    Lemma when_index:
      forall n k xs cs rs,
        Mod.when k xs cs rs ->
        (to_map xs n = absent
         /\ to_map cs n = absent
         /\ to_map rs n = absent)
        \/
        (exists x c,
            to_map xs n = present x
            /\ to_map cs n = present c
            /\ val_to_bool c = Some (negb k)
            /\ to_map rs n = absent)
        \/
        (exists x c,
            to_map xs n = present x
            /\ to_map cs n = present c
            /\ val_to_bool c = Some k
            /\ to_map rs n = present x).
    Proof.
      induction n; intros ** When.
      - inv When; repeat rewrite to_map_0; intuition.
        + right; left. do 2 eexists; intuition.
        + right; right. do 2 eexists; intuition.
      - inv When; repeat rewrite to_map_S; auto.
    Qed.

    Lemma lift1_index:
      forall n op t xs ys,
        Mod.lift1 op t xs ys ->
        (to_map xs n = absent /\ to_map ys n = absent)
        \/
        (exists x y,
            to_map xs n = present x
            /\ sem_unop op x t = Some y
            /\ to_map ys n = present y).
    Proof.
      induction n; intros ** Lift1.
      - inv Lift1; repeat rewrite to_map_0; intuition.
        right. do 2 eexists; intuition; auto.
      - inv Lift1; repeat rewrite to_map_S; auto.
    Qed.

    Lemma lift2_index:
      forall n op t1 t2 xs ys zs,
        Mod.lift2 op t1 t2 xs ys zs ->
        (to_map xs n = absent
         /\ to_map ys n = absent
         /\ to_map zs n = absent)
        \/
        (exists x y z,
            to_map xs n = present x
            /\ to_map ys n = present y
            /\ sem_binop op x t1 y t2 = Some z
            /\ to_map zs n = present z).
    Proof.
      induction n; intros ** Lift2.
      - inv Lift2; repeat rewrite to_map_0; intuition.
        right. do 3 eexists; intuition; auto.
      - inv Lift2; repeat rewrite to_map_S; auto.
    Qed.

    Lemma sem_clock_index:
      forall n H b ck bs,
        Mod.sem_clock H b ck bs ->
        (ck = Cbase
         /\ to_map b n = to_map bs n)
        \/
        (exists ck' x k c,
            ck = Con ck' x k
            /\ Sem.sem_clock_instant (to_map b n) (Sem.restr (hist_to_map H) n) ck' true
            /\ Sem.sem_var_instant (Sem.restr (hist_to_map H) n) x (present c)
            /\ val_to_bool c = Some k
            /\ to_map bs n = true)
        \/
        (exists ck' x k,
            ck = Con ck' x k
            /\ Sem.sem_clock_instant (to_map b n) (Sem.restr (hist_to_map H) n) ck' false
            /\ to_map bs n = false)
        \/
        (exists ck' x k c,
            ck = Con ck' x (negb k)
            /\ Sem.sem_clock_instant (to_map b n) (Sem.restr (hist_to_map H) n) ck' true
            /\ Sem.sem_var_instant (Sem.restr (hist_to_map H) n) x (present c)
            /\ val_to_bool c = Some k
            /\ to_map bs n = false).
    Proof.
      intros n H b ck; revert n H b; induction ck as [|ck ? x k].
      - inversion_clear 1 as [? ? ? Eb| | |].
        left; intuition.
        now rewrite Eb.
      - intro n; revert x k; induction n; intros x k H bk bk' Sem.
        + inversion_clear Sem as [|? ? ? ? ? ? ? ? ? SemCk Hvar
                                     |? ? ? ? ? ? ? SemCk
                                     |? ? ? ? ? ? ? ? ? SemCk Hvar].
          *{ right; left.
             apply sem_var_impl with (b:=to_map bk) in Hvar;
               unfold Sem.sem_var, Sem.lift in Hvar ; specialize (Hvar 0);
                 rewrite to_map_0 in Hvar.
             do 4 eexists; intuition; eauto.
             apply (IHck 0) in SemCk as [(Hck & E)
                                        |[(? & ? & ? & ? & Hck & ? & ? & ? & ?)
                                         |[(? & ? & ? & ? & ? & Ebk)
                                          |(? & ? & ? & ? & ? & ? & ? & ? & Ebk)]]];
               try rewrite Hck.
               + rewrite E, to_map_0; constructor.
               + econstructor; eauto.
               + rewrite to_map_0 in Ebk; discriminate.
               + rewrite to_map_0 in Ebk; discriminate.
           }
          *{ right; right; left.
             do 3 eexists; intuition.
             apply (IHck 0) in SemCk as [(Hck & E)
                                        |[(? & ? & ? & ? & ? & ? & ? & ? & Ebk)
                                         |[(? & ? & ? & Hck & ? & ?)
                                          |(? & ? & ? & ? & Hck & ? & ? & ? & ?)]]];
               try rewrite Hck.
             - rewrite E, to_map_0; constructor.
             - rewrite to_map_0 in Ebk; discriminate.
             - econstructor; eauto.
             - eapply Sem.Son_abs2; eauto.
           }
          *{ right; right; right.
             apply sem_var_impl with (b:=to_map bk) in Hvar;
               unfold Sem.sem_var, Sem.lift in Hvar; specialize (Hvar 0);
                 rewrite to_map_0 in Hvar.
             do 4 eexists; intuition; eauto.
             apply (IHck 0) in SemCk as [(Hck & E)
                                        |[(? & ? & ? & ? & Hck & ? & ? & ? & ?)
                                         |[(? & ? & ? & ? & ? & Ebk)
                                          |(? & ? & ? & ? & ? & ? & ? & ? & Ebk)]]];
               try rewrite Hck.
               + rewrite E, to_map_0; constructor.
               + econstructor; eauto.
               + rewrite to_map_0 in Ebk; discriminate.
               + rewrite to_map_0 in Ebk; discriminate.
           }
        + inversion_clear Sem; rewrite <-to_map_tl, hist_to_map_tl; eauto.
    Qed.

    Corollary sem_clock_impl:
      forall n H b ck bs,
        Mod.sem_clock H b ck bs ->
        Sem.sem_clock_instant (to_map b n) (Sem.restr (hist_to_map H) n) ck (to_map bs n).
    Proof.
      intros ** Sem.
      apply (sem_clock_index n) in Sem as [(Hck & E)
                                          |[(? & ? & ? & ? & Hck & ? & ? & ? & E)
                                           |[(? & ? & ? & Hck & ? & E)
                                            |(? & ? & ? & ? & Hck & ? & ? & ? & E)]]];
        rewrite Hck, E; try (now econstructor; eauto).
      eapply Sem.Son_abs2; eauto.
    Qed.

    Lemma sem_lexp_impl:
      forall H b e es,
        Mod.sem_lexp H b e es ->
        Sem.sem_lexp (to_map b) (hist_to_map H) e (to_map es).
    Proof.
      induction 1 as [? ? ? ? Hconst
                            |? ? ? ? ? Hvar
                            |? ? ? ? ? ? ? ? ? ? Hvar Hwhen
                            |? ? ? ? ? ? ? ? ? Hlift1
                            |? ? ? ? ? ? ? ? ? ? ? ? ? Hlift2]; intro n.
      - apply (const_index n) in Hconst; rewrite Hconst.
        destruct (to_map b n); now constructor.
      - apply sem_var_impl with (b := to_map b) in Hvar; eauto.
        unfold Sem.sem_var, Sem.lift in Hvar.
        specialize (Hvar n).
        destruct (to_map xs n) eqn: E; now constructor.
      - specialize (IHsem_lexp n).
        apply sem_var_impl with (b := to_map b) in Hvar.
        unfold Sem.sem_var, Sem.lift in Hvar.
        specialize (Hvar n).
        apply (when_index n) in Hwhen
          as [(Hes & Hxs & Hos)
             |[(? & ? & Hes & Hxs & ? & Hos)
              |(? & ? & Hes & Hxs & ? & Hos)]];
          rewrite Hos; rewrite Hes in IHsem_lexp; rewrite Hxs in Hvar;
            try (now econstructor; eauto).
        rewrite <-(Bool.negb_involutive k).
        eapply Sem.Swhen_abs1; eauto.
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
            econstructor; eauto.
    Qed.

    Lemma sem_laexp_index:
      forall n H b ck le es,
        Mod.sem_laexp H b ck le es ->
        (Sem.sem_clock_instant (to_map b n) (Sem.restr (hist_to_map H) n) ck false
         /\ Sem.sem_lexp_instant (to_map b n) (Sem.restr (hist_to_map H) n) le absent
         /\ to_map es n = absent)
        \/
        (exists e,
            Sem.sem_clock_instant (to_map b n) (Sem.restr (hist_to_map H) n) ck true
            /\ Sem.sem_lexp_instant (to_map b n) (Sem.restr (hist_to_map H) n) le (present e)
            /\ to_map es n = present e).
    Proof.
      induction n; intros ** Sem.
      - inversion_clear Sem as [? ? ? ? ? ? ? Sem' Hck|? ? ? ? ? ? Sem' Hck];
          apply sem_lexp_impl in Sem'; specialize (Sem' 0);
            repeat rewrite to_map_0; repeat rewrite to_map_0 in Sem';
              apply (sem_clock_impl 0) in Hck; rewrite to_map_0 in Hck.
        + right. eexists; intuition; auto.
        + left; intuition.
      - inversion_clear Sem as [? ? ? ? ? ? ? Sem'|? ? ? ? ? ? Sem'];
          apply sem_lexp_impl in Sem';
          rewrite to_map_S, hist_to_map_tl; eauto.
    Qed.

    Corollary sem_laexp_impl:
      forall H b e es ck,
        Mod.sem_laexp H b ck e es ->
        Sem.sem_laexp (to_map b) (hist_to_map H) ck e (to_map es).
    Proof.
      intros ** Sem n.
      apply (sem_laexp_index n) in Sem as [(? & ? & Hes)|(? & ? & ? & Hes)];
        rewrite Hes; now constructor.
    Qed.

    Lemma sem_laexps_index:
      forall n H b ck les ess,
        Mod.sem_laexps H b ck les ess ->
        (Sem.sem_clock_instant (to_map b n) (Sem.restr (hist_to_map H) n) ck false
         /\ Sem.sem_lexps_instant (to_map b n) (Sem.restr (hist_to_map H) n) les (to_maps ess n)
         /\ to_maps ess n = List.map (fun _ => absent) les)
        \/
        (Sem.sem_clock_instant (to_map b n) (Sem.restr (hist_to_map H) n) ck true
         /\ Sem.sem_lexps_instant (to_map b n) (Sem.restr (hist_to_map H) n) les (to_maps ess n)
         /\ Forall (fun e => e <> absent) (to_maps ess n)).
    Proof.
      induction n; intros ** Sem.
      - inversion_clear Sem as [? ? ? ? ? ? Sem' Hess Hck|? ? ? ? ? ? Sem' Hess Hck];
          apply (sem_clock_impl 0) in Hck; rewrite to_map_0 in Hck.
        + right. intuition; auto.
          *{ clear Hess. induction Sem' as [|? ? ? ? Sem]; simpl; constructor.
             - now apply sem_lexp_impl in Sem.
             - eapply IHSem', Mod.sem_laexps_cons; eauto.
           }
          * clear - Hess.
            induction ess; inv Hess; constructor; auto.
        + left. intuition; auto.
          *{ clear Hess. induction Sem' as [|? ? ? ? Sem]; simpl; constructor.
             - now apply sem_lexp_impl in Sem.
             - eapply IHSem', Mod.sem_laexps_cons; eauto.
           }
          * clear - Sem' Hess.
            induction Sem'; inv Hess; simpl; auto.
            f_equal; auto.
      - destruct b; inversion_clear Sem as [? ? ? ? ? ? Sem' Hess Hck|? ? ? ? ? ? Sem' Hess Hck];
          rewrite to_map_S, hist_to_map_tl, <-to_maps_tl; auto.
    Qed.

    Corollary sem_laexps_impl:
      forall H b ck es ess,
        Mod.sem_laexps H b ck es ess ->
        Sem.sem_laexps (to_map b) (hist_to_map H) ck es (to_maps ess).
    Proof.
      intros ** Sem n.
      apply (sem_laexps_index n) in Sem as [(? & ? & Hes)|(? & ? & Hes)].
      - eright; eauto.
      - assert (exists vs, to_maps ess n = List.map present vs) as (vs & ?).
        { clear - Hes.
          induction ess as [|es].
          - exists nil; auto.
          - simpl in *; inversion_clear Hes as [|? ? E].
            destruct (to_map es n) as [|v]; try now contradict E.
            apply IHess in H as (vs & ?).
            exists (v :: vs); simpl.
            f_equal; auto.
        }
        left with (cs := vs); eauto.
    Qed.

    Lemma merge_index:
      forall n xs ts fs rs,
        Mod.merge xs ts fs rs ->
        (to_map xs n = absent
         /\ to_map ts n = absent
         /\ to_map fs n = absent
         /\ to_map rs n = absent)
        \/
        (exists t,
            to_map xs n = present true_val
            /\ to_map ts n = present t
            /\ to_map fs n = absent
            /\ to_map rs n = present t)
        \/
        (exists f,
            to_map xs n = present false_val
            /\ to_map ts n = absent
            /\ to_map fs n = present f
            /\ to_map rs n = present f).
    Proof.
      induction n; intros ** Merge.
      - inv Merge; repeat rewrite to_map_0; intuition.
        + right; left. eexists; intuition.
        + right; right. eexists; intuition.
      - inv Merge; repeat rewrite to_map_S; auto.
    Qed.

    Lemma ite_index:
      forall n xs ts fs rs,
        Mod.ite xs ts fs rs ->
        (to_map xs n = absent
         /\ to_map ts n = absent
         /\ to_map fs n = absent
         /\ to_map rs n = absent)
        \/
        (exists t f,
            to_map xs n = present true_val
            /\ to_map ts n = present t
            /\ to_map fs n = present f
            /\ to_map rs n = present t)
        \/
        (exists t f,
            to_map xs n = present false_val
            /\ to_map ts n = present t
            /\ to_map fs n = present f
            /\ to_map rs n = present f).
    Proof.
      induction n; intros ** Ite.
      - inv Ite; repeat rewrite to_map_0; intuition.
        + right; left. do 2 eexists; intuition; discriminate.
        + right; right. do 2 eexists; intuition; discriminate.
      - inv Ite; repeat rewrite to_map_S; auto.
    Qed.

    Lemma sem_cexp_impl:
      forall H b e es,
        Mod.sem_cexp H b e es ->
        Sem.sem_cexp (to_map b) (hist_to_map H) e (to_map es).
    Proof.
      unfold Sem.sem_caexp, Sem.lift.
      induction 1 as [? ? ? ? ? ? ? ? ? Hvar Ht ? ? ? Hmerge
                    |? ? ? ? ? ? ? ? ? He Ht ? ? ? Hite
                    |? ? ? ? He]; intro n.
      - specialize (IHsem_cexp1 n).
        specialize (IHsem_cexp2 n).
        apply sem_var_impl with (b := to_map b) in Hvar; eauto.
        unfold Sem.sem_var, Sem.lift in Hvar.
        specialize (Hvar n).
        rename H0_ into Hf.
        apply (merge_index n) in Hmerge
          as [(Hxs & Hts & Hfs & Hos)
             |[(? & Hxs & Hts & Hfs & Hos)
              |(? & Hxs & Hts & Hfs & Hos)]];
          rewrite Hos; rewrite Hts in IHsem_cexp1; rewrite Hfs in IHsem_cexp2;
            rewrite Hxs in Hvar; try (now constructor; auto).
        apply Sem.Smerge_false; auto.

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
        Mod.sem_caexp H b ck le es ->
        (Sem.sem_clock_instant (to_map b n) (Sem.restr (hist_to_map H) n) ck false
         /\ Sem.sem_cexp_instant (to_map b n) (Sem.restr (hist_to_map H) n) le absent
         /\ to_map es n = absent)
        \/
        (exists e,
            Sem.sem_clock_instant (to_map b n) (Sem.restr (hist_to_map H) n) ck true
            /\ Sem.sem_cexp_instant (to_map b n) (Sem.restr (hist_to_map H) n) le (present e)
            /\ to_map es n = present e).
    Proof.
      induction n; intros ** Sem.
      - inversion_clear Sem as [? ? ? ? ? ? ? Sem' Hck|? ? ? ? ? ? Sem' Hck];
          apply sem_cexp_impl in Sem'; specialize (Sem' 0);
            repeat rewrite to_map_0; repeat rewrite to_map_0 in Sem';
              apply (sem_clock_impl 0) in Hck; rewrite to_map_0 in Hck.
        + right. eexists; intuition; auto.
        + left; intuition.
      - inversion_clear Sem as [? ? ? ? ? ? ? Sem'|? ? ? ? ? ? Sem'];
          apply sem_cexp_impl in Sem';
          repeat rewrite to_map_S; rewrite hist_to_map_tl; eauto.
    Qed.

    Corollary sem_caexp_impl:
      forall H b e es ck,
        Mod.sem_caexp H b ck e es ->
        Sem.sem_caexp (to_map b) (hist_to_map H) ck e (to_map es).
    Proof.
      intros ** Sem n.
      apply (sem_caexp_index n) in Sem as [(? & ? & Hes)|(? & ? & ? & Hes)];
        rewrite Hes; now constructor.
    Qed.

    Lemma to_map_reset:
      forall n xs,
        to_map (Mod.reset_of xs) n = Sem.reset_of (to_map xs) n.
    Proof.
      induction n; intros.
      - unfold_Stv xs; unfold Sem.reset_of;
          rewrite unfold_Stream at 1; simpl; rewrite to_map_0; auto.
      - unfold_Stv xs; unfold Sem.reset_of;
          rewrite unfold_Stream at 1; simpl; auto;
            eapply IHn.
    Qed.

    Lemma fby_impl:
      forall n c xs,
      to_map (Mod.fby c xs) n = fby c (to_map xs) n.
    Proof.
      induction n; intros.
      - unfold_Stv xs; rewrite unfold_Stream at 1;
          unfold fby; simpl; now rewrite to_map_0.
      - unfold_Stv xs; rewrite unfold_Stream at 1;
          unfold fby; simpl; repeat rewrite to_map_S;
            rewrite IHn; unfold fby;
              destruct (to_map xs n); auto; f_equal;
                clear IHn; induction n; simpl; auto;
                  rewrite to_map_S; destruct (to_map xs n); auto.
    Qed.

    Lemma sem_clock_to_map:
      forall xss,
        Sem.clock_of (to_maps xss) (to_map (Mod.clocks_of xss)).
    Proof.
      split; intros ** H.
      - revert dependent xss; induction n; intros; induction xss as [|xs];
          rewrite unfold_Stream at 1; simpl in *;
          try rewrite to_map_0; try rewrite to_map_S; auto.
        + inversion_clear H as [|? ? ToMap Forall].
          apply andb_true_intro; split.
          * unfold_St xs; rewrite to_map_0 in ToMap.
            apply Bool.negb_true_iff; rewrite not_equiv_decb_equiv; intro E.
            contradiction.
          * apply IHxss in Forall.
            clear - Forall; induction xss as [|xs]; simpl; auto.
        + inversion_clear H.
          apply IHn. constructor.
          * now rewrite to_map_tl.
          * fold (@to_maps value).
            now rewrite to_maps_tl.
      - revert dependent xss; induction n; intros; induction xss as [|xs];
          simpl in *; constructor.
        + rewrite unfold_Stream in H at 1; simpl in H;
            rewrite to_map_0 in H; apply andb_prop in H as [].
          unfold_St xs; rewrite to_map_0; simpl in *.
          intro; subst; discriminate.
        + apply IHxss.
          rewrite unfold_Stream in H at 1; simpl in H;
            rewrite to_map_0 in H; apply andb_prop in H as [? Forall].
          clear - Forall; induction xss; rewrite unfold_Stream at 1; simpl;
            now rewrite to_map_0.
        + rewrite unfold_Stream in H at 1; simpl in H; rewrite to_map_S in H.
          apply IHn in H; inv H.
          now rewrite <-to_map_tl.
        + rewrite unfold_Stream in H at 1; simpl in H; rewrite to_map_S in H.
          apply IHn in H; inv H.
          now rewrite <-to_maps_tl.
    Qed.

    Remark count_true_not_0:
      forall r n,
        count (to_map (true ::: r)) n <> 0.
    Proof.
      intros; induction n; simpl.
      - omega.
      - rewrite to_map_S.
        destruct (to_map r n); auto.
    Qed.

    Remark count_true_not_0':
      forall n r,
        to_map r n = true ->
        count (to_map r) n <> 0.
    Proof.
      induction n; simpl; intros r E; try rewrite E; auto.
    Qed.

    Remark to_map_mask_true_0:
      forall n r xs,
      to_map r n = true ->
      to_map (Mod.mask absent 0 r xs) n = absent.
    Proof.
      induction n; intros ** E; rewrite unfold_Stream at 1; simpl;
        unfold_Stv r; unfold_Stv xs; auto; try rewrite to_map_S.
      - rewrite to_map_0 in E; discriminate.
      - pose proof (to_map_const absent); auto.
      - pose proof (to_map_const absent); auto.
      - apply IHn.
        rewrite to_map_S in E; auto.
      - apply IHn.
        rewrite to_map_S in E; auto.
    Qed.

    Lemma count_true_shift:
      forall n r,
        count (to_map (true ::: r)) n
        = if to_map r n then count (to_map r) n else S (count (to_map r) n).
    Proof.
      induction n; simpl; intros.
      - destruct (to_map r 0); auto.
      - specialize (IHn r).
        rewrite to_map_S.
        destruct (to_map r n) eqn: E';
          destruct (to_map r (S n)); rewrite IHn; auto.
    Qed.

    Lemma count_false_shift:
      forall n r,
        count (to_map (false ::: r)) n
        = if to_map r n then count (to_map r) n - 1 else count (to_map r) n.
    Proof.
      induction n; simpl; intros.
      - destruct (to_map r 0); auto.
      - specialize (IHn r).
        rewrite to_map_S.
        destruct (to_map r n) eqn: E';
          destruct (to_map r (S n)); rewrite IHn; try omega.
        + apply Minus.minus_Sn_m, count_true_ge_1; auto.
        + rewrite Minus.minus_Sn_m; try omega.
          apply count_true_ge_1; auto.
    Qed.

    Lemma to_map_mask_false_true:
      forall n r xs k k',
        to_map r n = false ->
        count (to_map (true ::: r)) n = S k ->
        to_map (Mod.mask absent k' r xs) n
        = if EqNat.beq_nat k k' then to_map xs n else absent.
    Proof.
      intros ** E C.
      rewrite count_true_shift, E in C; injection C; clear C; intro C.
      revert k' k r xs E C; induction n; simpl; intros.
      - rewrite E in C.
        destruct (EqNat.beq_nat k k') eqn: E'.
        + apply EqNat.beq_nat_true in E'; subst.
          unfold_Stv r; unfold_St xs; rewrite unfold_Stream at 1;
            simpl; rewrite <-E'; repeat rewrite to_map_0; auto.
          rewrite to_map_0 in E; discriminate.
        + apply EqNat.beq_nat_false in E'.
          unfold_Stv r; unfold_St xs; rewrite unfold_Stream at 1;
            destruct k' as [|[]]; simpl; try (exfalso; now apply E').
          * pose proof (to_map_const absent); auto.
          * apply to_map_0.
      - destruct (EqNat.beq_nat k k') eqn: E'.
        + apply EqNat.beq_nat_true in E'; subst.
          unfold_Stv r; unfold_St xs; rewrite unfold_Stream at 1;
            destruct k' as [|[]]; simpl; repeat rewrite to_map_S; rewrite E in E';
              try discriminate; rewrite to_map_S in E.
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
              repeat rewrite to_map_S; rewrite to_map_S in E;
                try (exfalso; now apply E').
          * pose proof (to_map_const absent); auto.
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

    Lemma to_map_mask_true_false:
      forall n r xs k k',
        to_map r n = true ->
        count (to_map (false ::: r)) n = k ->
        to_map (Mod.mask absent (S k') r xs) n
        = if EqNat.beq_nat k k' then to_map xs n else absent.
    Proof.
      intros ** E C.
      rewrite count_false_shift, E in C.
      revert k' k r xs E C; induction n; simpl; intros.
      - rewrite E in C.
        destruct (EqNat.beq_nat k k') eqn: E'.
        + apply EqNat.beq_nat_true in E'; subst.
          unfold_Stv r; unfold_St xs; rewrite unfold_Stream at 1;
            simpl; rewrite <-E'; repeat rewrite to_map_0; auto.
          rewrite to_map_0 in E; discriminate.
        + apply EqNat.beq_nat_false in E'.
          unfold_Stv r; unfold_St xs; rewrite unfold_Stream at 1;
            destruct k' as [|[]]; simpl; try (exfalso; now apply E').
          * pose proof (to_map_const absent); auto.
          * apply to_map_0.
      - destruct (EqNat.beq_nat k k') eqn: E'.
        + apply EqNat.beq_nat_true in E'; subst.
          unfold_Stv r; unfold_St xs; rewrite unfold_Stream at 1;
            destruct k' as [|[]]; simpl; repeat rewrite to_map_S; rewrite E in E';
              try discriminate; rewrite to_map_S in E; simpl in E';
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
              repeat rewrite to_map_S; rewrite to_map_S in E;
                simpl in E'; try rewrite <-Minus.minus_n_O in E';
                try (exfalso; now apply E').
          * apply to_map_mask_true_0; auto.
          * erewrite IHn; eauto.
            rewrite count_true_shift, E in E'.
            rewrite <-plus_n_O.
            apply count_true_not_0' in E.
            destruct (count (to_map r) n) as [|[]];
              try (exfalso; now apply E); try (exfalso; now apply E').
            auto.
          * erewrite IHn; eauto.
            rewrite count_true_shift, E in E'.
            apply count_true_not_0' in E.
            destruct (count (to_map r) n) as [|[|]];
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

    Lemma to_map_mask_same:
      forall n b r xs k k',
        to_map r n = b ->
        count (to_map (b ::: r)) n = k ->
        to_map (Mod.mask absent k' r xs) n
        = if EqNat.beq_nat k k' then to_map xs n else absent.
    Proof.
      intros ** E C.
      destruct b.
      - rewrite count_true_shift, E in C.
        revert k' k r xs E C; induction n; simpl; intros.
        + rewrite E in C.
          destruct (EqNat.beq_nat k k') eqn: E'.
          * apply EqNat.beq_nat_true in E'; subst.
            unfold_Stv r; unfold_St xs; rewrite unfold_Stream at 1;
              simpl; rewrite <-E'; repeat rewrite to_map_0; auto.
            rewrite to_map_0 in E; discriminate.
          *{ apply EqNat.beq_nat_false in E'.
             unfold_Stv r; unfold_St xs; rewrite unfold_Stream at 1;
               destruct k' as [|[]]; simpl; try (exfalso; now apply E').
             - pose proof (to_map_const absent); auto.
             - apply to_map_0.
           }
        + destruct (EqNat.beq_nat k k') eqn: E'.
          *{ apply EqNat.beq_nat_true in E'; subst.
             unfold_Stv r; unfold_St xs; rewrite unfold_Stream at 1;
               destruct k' as [|[]]; simpl; repeat rewrite to_map_S; rewrite E in E';
                 try discriminate; rewrite to_map_S in E.
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
                 repeat rewrite to_map_S; rewrite to_map_S in E;
                   try (exfalso; now apply E').
             - pose proof (to_map_const absent); auto.
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
              simpl; rewrite <-E'; repeat rewrite to_map_0; auto.
            rewrite to_map_0 in E; discriminate.
          *{ apply EqNat.beq_nat_false in E'.
             unfold_Stv r; unfold_St xs; rewrite unfold_Stream at 1;
               destruct k' as [|[]]; simpl; try (exfalso; now apply E').
             - pose proof (to_map_const absent); auto.
             - apply to_map_0.
           }
        + destruct (EqNat.beq_nat k k') eqn: E'.
          *{ apply EqNat.beq_nat_true in E'; subst.
             unfold_Stv r; unfold_St xs; rewrite unfold_Stream at 1;
               destruct k' as [|[]]; simpl; repeat rewrite to_map_S; rewrite E in E';
                 try discriminate; rewrite to_map_S in E.
             - inv E'; exfalso; eapply count_true_not_0; eauto.
             - erewrite to_map_mask_false_true; eauto;
                 rewrite <-EqNat.beq_nat_refl; auto.
             - erewrite to_map_mask_false_true; eauto;
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
                 repeat rewrite to_map_S; rewrite to_map_S in E;
                   try (exfalso; now apply E').
             - pose proof (to_map_const absent); auto.
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
        erewrite H; eauto; unfold mask; simpl; rewrite to_map_S;
        repeat match goal with
               | H: to_map _ _ = _ |- _ => rewrite H
               | H: count ?x _ = _ |- _ => rewrite H
               | H:  EqNat.beq_nat _ _ = _ |- _ => rewrite H
               end; auto].

    Lemma mask_impl:
      forall k r xss opaque n,
        length opaque = length xss ->
        Sem.absent_list opaque ->
        to_maps (List.map (Mod.mask_v k r) xss) n
        = mask opaque k (to_map r) (to_maps xss) n.
    Proof.
      induction xss as [|xs], opaque as [|o];
        simpl; intros ** Length Abs; inv Length; inv Abs.
      - unfold mask.
        destruct (EqNat.beq_nat k (count (to_map r) n)); auto.
      - induction n.
        + unfold_St xs; unfold_Stv r; unfold Mod.mask_v, mask;
            rewrite unfold_Stream at 1; simpl;
            destruct k as [|[]]; simpl; f_equal;
              erewrite IHxss; eauto; unfold mask; auto.
        + unfold_St xs; unfold_Stv r; unfold Mod.mask_v, mask.
          *{ rewrite unfold_Stream at 1; simpl.
             destruct k as [|[]]; simpl.
             - repeat rewrite to_map_S.
               destruct (to_map r n) eqn: E.
               + auto_f_equal IHxss.
                 pose proof (to_map_const absent); auto.
               + destruct (count (to_map (true ::: r)) n) eqn: E'.
                 * exfalso; eapply count_true_not_0; eauto.
                 * auto_f_equal IHxss.
                   pose proof (to_map_const absent); auto.
             - repeat rewrite to_map_S.
               destruct (to_map r n) eqn: E.
               + destruct (count (to_map (true ::: r)) n) eqn: E'.
                 * exfalso; eapply count_true_not_0; eauto.
                 * auto_f_equal IHxss.
                   apply to_map_mask_true_0; auto.
               + destruct (count (to_map (true ::: r)) n) as [|[]] eqn: E'.
                 * exfalso; eapply count_true_not_0; eauto.
                 * auto_f_equal IHxss.
                   erewrite to_map_mask_false_true; eauto; auto.
                 * auto_f_equal IHxss.
                   erewrite to_map_mask_false_true; eauto; auto.
             - repeat rewrite to_map_S.
               destruct (to_map r n) eqn: E.
               + destruct (count (to_map (true ::: r)) n) eqn: E'.
                 * exfalso; eapply count_true_not_0; eauto.
                 *{ destruct (EqNat.beq_nat n0 n1) eqn: E''; auto_f_equal IHxss.
                    - erewrite to_map_mask_same; eauto.
                      apply EqNat.beq_nat_true, eq_S, EqNat.beq_nat_true_iff in E'';
                        rewrite NPeano.Nat.eqb_sym, E''; auto.
                    - erewrite to_map_mask_same; eauto.
                      apply EqNat.beq_nat_false, not_eq_S, EqNat.beq_nat_false_iff in E'';
                        rewrite NPeano.Nat.eqb_sym, E''; auto.
                  }
               + destruct (count (to_map (true ::: r)) n) as [|[]] eqn: E'.
                 * exfalso; eapply count_true_not_0; eauto.
                 * auto_f_equal IHxss.
                   erewrite to_map_mask_false_true; eauto; auto.
                 *{ destruct (EqNat.beq_nat n0 n1) eqn: E''; auto_f_equal IHxss.
                    - erewrite to_map_mask_false_true; eauto.
                      apply EqNat.beq_nat_true, eq_S, EqNat.beq_nat_true_iff in E'';
                        rewrite NPeano.Nat.eqb_sym, E''; auto.
                    - erewrite to_map_mask_false_true; eauto.
                      apply EqNat.beq_nat_false, not_eq_S, EqNat.beq_nat_false_iff in E'';
                        rewrite NPeano.Nat.eqb_sym, E''; auto.
                  }
           }

          *{ rewrite unfold_Stream at 1; simpl.
             destruct k as [|[]]; simpl.
             - repeat rewrite to_map_S.
               destruct (to_map r n) eqn: E.
               + auto_f_equal IHxss.
                 apply to_map_mask_true_0; auto.
               + destruct (count (to_map (false ::: r)) n) eqn: E';
                   auto_f_equal IHxss; erewrite to_map_mask_same; eauto; auto.
             - repeat rewrite to_map_S.
               destruct (to_map r n) eqn: E.
               + destruct (count (to_map (false ::: r)) n) eqn: E';
                   auto_f_equal IHxss;
                   erewrite to_map_mask_true_false; eauto; auto.
               + destruct (count (to_map (false ::: r)) n) as [|[]] eqn: E';
                   auto_f_equal IHxss; erewrite to_map_mask_same; eauto; auto.
             - repeat rewrite to_map_S.
               destruct (to_map r n) eqn: E.
               + destruct (count (to_map (false ::: r)) n) eqn: E'.
                 * auto_f_equal IHxss.
                   erewrite to_map_mask_true_false; eauto; auto.
                 *{ destruct (EqNat.beq_nat n0 n1) eqn: E''; auto_f_equal IHxss.
                    - erewrite to_map_mask_true_false; eauto.
                      apply EqNat.beq_nat_true, eq_S,
                      EqNat.beq_nat_true_iff in E'';
                        rewrite NPeano.Nat.eqb_sym, E''; auto.
                    - erewrite to_map_mask_true_false; eauto.
                      apply EqNat.beq_nat_false, not_eq_S,
                      EqNat.beq_nat_false_iff in E'';
                        rewrite NPeano.Nat.eqb_sym, E''; auto.
                  }
               + destruct (count (to_map (false ::: r)) n) as [|[]] eqn: E'.
                 * auto_f_equal IHxss.
                   erewrite to_map_mask_same; eauto; auto.
                 * auto_f_equal IHxss.
                   erewrite to_map_mask_same; eauto; auto.
                 *{ destruct (EqNat.beq_nat n0 n1) eqn: E''; auto_f_equal IHxss.
                    - erewrite to_map_mask_same; eauto.
                      apply EqNat.beq_nat_true, eq_S, eq_S,
                      EqNat.beq_nat_true_iff in E'';
                        rewrite NPeano.Nat.eqb_sym, E''; auto.
                    - erewrite to_map_mask_same; eauto.
                      apply EqNat.beq_nat_false, not_eq_S, not_eq_S,
                      EqNat.beq_nat_false_iff in E'';
                        rewrite NPeano.Nat.eqb_sym, E''; auto.
                  }
           }
    Qed.

    Remark length_all_absent:
      forall A (xss: list (Stream A)) n,
        length (Sem.all_absent (to_maps xss n)) = length xss.
    Proof.
      induction xss; simpl; auto.
    Qed.

    Theorem implies:
      (forall H b e,
          Mod.sem_equation G H b e ->
          Sem.sem_equation G (to_map b) (hist_to_map H) e)
      /\
      (forall f xss oss,
          Mod.sem_node G f xss oss ->
          Sem.sem_node G f (to_maps xss) (to_maps oss))
      /\
      (forall f r xss oss,
          Mod.sem_reset G f r xss oss ->
          Sem.sem_reset G f (to_map r) (to_maps xss) (to_maps oss)).
    Proof.
      apply Mod.sem_equation_node_ind.
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
        + eapply Sem.sem_reset_compat.
          * intro; apply to_map_reset.
          * eauto.
      - econstructor; auto; subst.
        + apply sem_laexp_impl; eauto.
        + unfold Sem.sem_var, Sem.lift; intro.
          rewrite <-fby_impl.
          apply sem_var_impl; auto.
          exact (to_map b).
      - intros ** IHNode.
        constructor; intro.
        specialize (IHNode n).
        pose proof (mask_impl n r xss) as Hxss.
        pose proof (mask_impl n r yss) as Hyss.
        eapply Sem.sem_node_compat.
        + intro; apply Hxss;
            [apply length_all_absent | apply Sem.all_absent_spec].
        + intro; apply Hyss;
            [apply length_all_absent | apply Sem.all_absent_spec].
        + auto.
      - intros ** Hin Hout Same ? ?. econstructor; eauto.
        + apply sem_clock_to_map.
        + apply sem_vars_impl; eauto.
        + apply sem_vars_impl; eauto.
        + now apply Mod.same_clock_app_l, same_clock_impl in Same.
        + now apply Mod.same_clock_app_r, same_clock_impl in Same.
        + apply same_clock_app_impl; auto.
          * intro; subst.
            apply Forall2_length in Hin; simpl in *.
            unfold Mod.idents in Hin; rewrite map_length in Hin.
            pose proof n.(n_ingt0) as Nin.
            rewrite Hin in Nin; contradict Nin; apply Lt.lt_irrefl.
          * intro; subst.
            apply Forall2_length in Hout; simpl in *.
            unfold Mod.idents in Hout; rewrite map_length in Hout.
            pose proof n.(n_outgt0) as Nout.
            rewrite Hout in Nout; contradict Nout; apply Lt.lt_irrefl.
    Qed.

  End Global.

End COINDTONATMAP.
