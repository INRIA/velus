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

    Fixpoint to_maps {A} (xss: list (Stream A)) : stream (list A) :=
      match xss with
      | [] => fun n => []
      | xs :: xss => fun n => to_map xs n :: to_maps xss n
      end.

    Fact to_maps_app:
      forall A (xss yss: list (Stream A)) n,
        to_maps (xss ++ yss) n = to_maps xss n ++ to_maps yss n.
    Proof.
      intros.
      induction xss; simpl; auto.
      f_equal; auto.
    Qed.

    Definition hist_to_map (H: Mod.history) : Sem.history :=
      PM.map (fun xs => fun n => Str_nth n xs) H.

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
        apply IHxss; auto.
        eapply Mod.same_clock_cons; eauto.
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

    Lemma sem_lexp_impl:
      forall H b e es ck,
        Mod.sem_lexp H b e es ->
        Sem.sem_laexp (to_map b) (hist_to_map H) ck e (to_map es).
    Proof.
      unfold Sem.sem_laexp, Sem.lift.
      induction 1 as [? ? ? ? Hconst
                    |? ? ? ? ? Hvar
                    |? ? ? ? ? ? ? ? ? ? Hvar Hwhen
                    |? ? ? ? ? ? ? ? ? Hlift1
                    |? ? ? ? ? ? ? ? ? ? ? ? ? Hlift2]; intro n.
      - apply (const_index n) in Hconst; rewrite Hconst.
        destruct (to_map b n).
        + constructor.
          * now constructor.
          * admit.
        + constructor.
          admit.
      - destruct (to_map xs n) eqn: E.
        + constructor.
          admit.
        + constructor.
          * constructor.
            apply sem_var_impl with (b := to_map b) in Hvar.
            unfold Sem.sem_var, Sem.lift in Hvar.
            specialize (Hvar n).
            rewrite E in Hvar; apply Hvar.
          * admit.
      - apply (when_index n) in Hwhen
          as [(? & ? & Hos)
             |[(? & ? & ? & ? & ? & Hos)
              |(? & ? & Hes & Hxs & ? & Hos)]]; rewrite Hos.
        + constructor.
          admit.
        + constructor.
          admit.
        + constructor.
          * apply sem_var_impl with (b := to_map b) in Hvar.
            unfold Sem.sem_var, Sem.lift in Hvar.
            specialize (Hvar n).
            rewrite Hxs in Hvar.
            econstructor; eauto.
            specialize (IHsem_lexp n); rewrite Hes in IHsem_lexp;
              inv IHsem_lexp; auto.
          * admit.
      - apply (lift1_index n) in Hlift1
          as [(? & Hos)|(? & ? & Hes & ? & Hos)]; rewrite Hos.
        + constructor.
          admit.
        + constructor.
          * econstructor; eauto.
            specialize (IHsem_lexp n); rewrite Hes in IHsem_lexp;
              inv IHsem_lexp; auto.
          * admit.
      - apply (lift2_index n) in Hlift2
          as [(? & ? & Hos)|(? & ? & ? & Hes1 & Hes2 & ? & Hos)]; rewrite Hos.
        + constructor.
          admit.
        + constructor.
          * specialize (IHsem_lexp1 n); rewrite Hes1 in IHsem_lexp1;
              inv IHsem_lexp1.
            specialize (IHsem_lexp2 n); rewrite Hes2 in IHsem_lexp2;
              inv IHsem_lexp2.
           econstructor; eauto.
          * admit.
    Qed.

    Corollary sem_lexps_impl:
      forall H b ck es ess,
        Forall2 (Mod.sem_lexp H b) es ess ->
        Sem.sem_laexps (to_map b) (hist_to_map H) ck es (to_maps ess).
    Proof.
      unfold Sem.sem_laexps, Sem.lift; intros.
      admit.
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
      forall H b e es ck,
        Mod.sem_cexp H b e es ->
        Sem.sem_caexp (to_map b) (hist_to_map H) ck e (to_map es).
    Proof.
      unfold Sem.sem_caexp, Sem.lift.
      induction 1 as [? ? ? ? ? ? ? ? ? Hvar Ht ? ? ? Hmerge
                    |? ? ? ? ? ? ? ? ? He Ht ? ? ? Hite
                    |? ? ? ? He]; intro n.
      - rename H0_ into Hf.
        apply (merge_index n) in Hmerge
          as [(? & ? & ? & Hos)
             |[(? & Hxs & Hts & Hfs & Hos)
              |(? & Hxs & Hts & Hfs & Hos)]]; rewrite Hos.
        + constructor.
          admit.
        + constructor.
          *{ constructor.
             - rewrite <-Hxs; apply sem_var_impl; auto.
               exact (to_map b).
             - specialize (IHsem_cexp1 n).
               rewrite Hts in IHsem_cexp1.
               inv IHsem_cexp1; auto.
             - specialize (IHsem_cexp2 n).
               rewrite Hfs in IHsem_cexp2.
               inv IHsem_cexp2; auto.
               admit.
           }
          * admit.
        + constructor.
          *{ apply Sem.Smerge_false.
             - rewrite <-Hxs; apply sem_var_impl; auto.
               exact (to_map b).
             - specialize (IHsem_cexp1 n).
               rewrite Hts in IHsem_cexp1.
               inv IHsem_cexp1.
               admit.
             - specialize (IHsem_cexp2 n).
               rewrite Hfs in IHsem_cexp2.
               inv IHsem_cexp2; auto.
           }
          * admit.

      - apply (ite_index n) in Hite
          as [(? & ? & ? & Hos)
             |[(ct & cf & Hes & Hts & Hfs & Hos)
              |(ct & cf & Hes & Hts & Hfs & Hos)]]; rewrite Hos.
        + constructor.
          admit.
        + constructor.
          *{ change (present ct) with (if true then present ct else present cf).
             econstructor.
             - eapply sem_lexp_impl with (ck := ck) in He.
               unfold Sem.sem_laexp, Sem.lift in He.
               specialize (He n); rewrite Hes in He.
               inv He; eauto.
             - specialize (IHsem_cexp1 n); rewrite Hts in IHsem_cexp1;
                 inv IHsem_cexp1; auto.
             - specialize (IHsem_cexp2 n); rewrite Hfs in IHsem_cexp2;
                 inv IHsem_cexp2; auto.
             - apply val_to_bool_true.
           }
          * admit.
        + constructor.
          *{ change (present cf) with (if false then present ct else present cf).
             econstructor.
             - eapply sem_lexp_impl with (ck := ck) in He.
               unfold Sem.sem_laexp, Sem.lift in He.
               specialize (He n); rewrite Hes in He.
               inv He; eauto.
             - specialize (IHsem_cexp1 n); rewrite Hts in IHsem_cexp1;
                 inv IHsem_cexp1; auto.
             - specialize (IHsem_cexp2 n); rewrite Hfs in IHsem_cexp2;
                 inv IHsem_cexp2; auto.
             - apply val_to_bool_false.
           }
          * admit.

      - apply sem_lexp_impl with (ck := ck) in He.
        unfold Sem.sem_laexp, Sem.lift in He.
        specialize (He n).
        inv He.
        + constructor.
          * constructor; auto.
          * admit.
        + constructor.
          admit.
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

    Lemma sem_equation_impl:
      forall H b e,
        Mod.sem_equation G H b e ->
        Sem.sem_equation G (to_map b) (hist_to_map H) e.
    Proof.
      intros ** Sem.
      induction Sem as [? ? ? ? ? ? He
                      |
                      |
                      |
                      |? ? ? ? HNode IHNode
                      | ]
                         using Mod.sem_equation_mult with
          (P_node := fun f xss oss => Mod.sem_node G f xss oss ->
                                   Sem.sem_node G f (to_maps xss) (to_maps oss))
          (P_reset := fun f r xss oss => (* Mod.sem_reset G f r xss oss -> *)
                                      Sem.sem_reset G f (to_map r) (to_maps xss) (to_maps oss)).
      - econstructor.
        + apply sem_var_impl; eauto.
        + apply sem_cexp_impl; auto.
      - econstructor; auto.
        + apply sem_lexps_impl; eauto.
        + apply sem_vars_impl; eauto.
      - econstructor; auto.
        + apply sem_lexps_impl; eauto.
        + apply sem_vars_impl; eauto.
        + apply sem_var_impl; eauto.
        + admit.
      - econstructor; auto.
        + apply sem_lexp_impl; eauto.
        + admit.
      - constructor; intro.
        apply (IHNode n) in HNode. admit.
      - admit.
    Qed.

    Theorem implies:
      forall f xss oss,
        Mod.sem_node G f xss oss ->
        Sem.sem_node G f (to_maps xss) (to_maps oss).
    Proof.
      intros ** Sem.
      induction Sem as [
                      |
                      |
                      |
                      |
                      | ? ? ? ? ? Find Hin Hout Same]
                         using Mod.sem_node_mult with
          (P_equation := fun H b e => True)
          (P_reset := fun f r xss oss => True).
      - auto.
      - auto.
      - auto.
      - auto.
      - auto.
      - econstructor; eauto.
        + apply Sem.clock_of_equiv.
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
        + admit.
        + admit.
    Qed.


  End Global.

End COINDTONATMAP.
