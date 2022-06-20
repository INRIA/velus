From Coq Require Import Streams.
From Coq Require Import List.
Import List.ListNotations.
Open Scope list_scope.

From Coq Require Import Sorting.Permutation.
From Coq Require Import Setoid.
From Coq Require Import Morphisms.

From Coq Require Import FSets.FMapPositive.
From Velus Require Import Common.
From Velus Require Import CommonList.
From Velus Require Import FunctionalEnvironment.
From Velus Require Import Operators.
From Velus Require Import CoindStreams IndexedStreams.
From Velus Require Import CoindIndexed.
From Velus Require Import Clocks.
From Velus Require Import Lustre.StaticEnv.
From Velus Require Import Lustre.LSyntax Lustre.LTyping Lustre.LClocking Lustre.LCausality Lustre.LOrdered.
From Velus Require Import Lustre.LSemantics Lustre.LClockedSemantics.

(** * Clock Correctness Proof *)

Module Type LCLOCKCORRECTNESS
       (Import Ids   : IDS)
       (Import Op    : OPERATORS)
       (Import OpAux : OPERATORS_AUX Ids Op)
       (Import Cks   : CLOCKS        Ids Op OpAux)
       (Import Senv  : STATICENV     Ids Op OpAux Cks)
       (Import Syn   : LSYNTAX Ids Op OpAux Cks Senv)
       (Import Typ   : LTYPING Ids Op OpAux Cks Senv Syn)
       (Import Clo   : LCLOCKING Ids Op OpAux Cks Senv Syn)
       (Import LCA   : LCAUSALITY Ids Op OpAux Cks Senv Syn)
       (Import Lord  : LORDERED Ids Op OpAux Cks Senv Syn)
       (Import CStr  : COINDSTREAMS Ids Op OpAux Cks)
       (Import Sem   : LSEMANTICS Ids Op OpAux Cks Senv Syn Lord CStr)
       (Import CkSem : LCLOCKEDSEMANTICS Ids Op OpAux Cks Senv Syn Clo Lord CStr Sem).

  Import CStr.
  Module IStr := IndexedStreamsFun Ids Op OpAux Cks.
  Module Import CIStr := CoindIndexedFun Ids Op OpAux Cks CStr IStr.

  Import List.

  Definition sem_clock_inputs {PSyn prefs} (G : @global PSyn prefs) (f : ident) (xs : list (Stream svalue)): Prop :=
    exists H n,
      find_node f G = Some n /\
      Forall2 (sem_var H) (idents (n_in n)) xs /\
      Forall2 (fun xc => sem_clock H (clocks_of xs) (snd xc))
              (map (fun '(x, (_, ck, _)) => (x, ck)) (n_in n)) (map abstract_clock xs).

  Lemma sem_clock_inputs_cons {PSyn prefs} :
    forall types (nodes : list (@node PSyn prefs)) f n ins,
      n_name n <> f ->
      sem_clock_inputs (Global types nodes) f ins <-> sem_clock_inputs (Global types (n :: nodes)) f ins.
  Proof.
    intros * Hname.
    split; intros (H & n' & Hfind &?&?);
      exists H, n'; repeat split; auto.
    - rewrite find_node_other; eauto.
    - erewrite <- find_node_other; eauto.
  Qed.

  Lemma inputs_clocked_vars {PSyn prefs} :
    forall types (nodes : list (@node PSyn prefs)) n H f ins,
      sem_clock_inputs (Global types (n :: nodes)) f ins ->
      n_name n = f ->
      wc_env (map (fun '(x, (_, ck, _)) => (x, ck)) (n_in n)) ->
      Forall2 (sem_var H) (idents (n_in n)) ins ->
      Forall2 (fun xc => sem_clock H (clocks_of ins) (snd xc)) (map (fun '(x, (_, ck, _)) => (x, ck)) (n_in n)) (map abstract_clock ins).
  Proof.
    intros * (H'&n'& Hfind & Hv & Hscin) Hnf Wcin Hins; subst.
    rewrite find_node_now in Hfind; auto. inv Hfind.
    pose proof (sem_var_env_eq _ _ _ _ Hins Hv) as Horel.
    eapply Forall2_impl_In; [|eauto]. intros; simpl in *.
    eapply sem_clock_same_find; eauto.
    - unfold wc_env in Wcin. simpl_In. simpl_Forall. eapply Wcin.
    - unfold idents in *. simpl_Forall. auto.
  Qed.

  Lemma sem_clocks_det : forall H H' b ins outs vins vouts ss,
      wc_env (map (fun '(x, (_, ck, _)) => (x, ck)) (ins ++ outs)) ->
      Forall2 (sem_var H) (idents ins) vins ->
      Forall2 (sem_var H) (idents outs) vouts ->
      Forall2 (sem_var H') (idents ins) vins ->
      Forall2 (sem_var H') (idents outs) vouts ->
      Forall2 (fun xc => sem_clock H b (snd xc)) (map (fun '(x, (_, ck, _)) => (x, ck)) outs) ss ->
      Forall2 (fun xs => sem_clock H' b (snd xs)) (map (fun '(x, (_, ck, _)) => (x, ck)) outs) ss.
  Proof.
    intros * Hwc Hi1 Ho1 Hi2 Ho2 Hck.
    eapply Forall2_impl_In; [|eauto]. intros [? ?] ? Hin1 Hin2 Hsc.
    rewrite map_app in Hwc. assert (Hwc':=Hwc). apply Forall_app_weaken in Hwc.
    eapply Forall_forall in Hin1; eauto; simpl in *.
    rewrite sem_clock_equiv in *. clear Hck Hwc Hwc' Hin2.
    intros n. specialize (Hsc n).
    eapply Forall2_app in Ho1; [|eapply Hi1]. eapply Forall2_app in Ho2; [|eapply Hi2]. clear Hi1 Hi2.
    unfold idents in Ho1, Ho2. rewrite <- map_app, Forall2_map_1 in Ho1, Ho2.
    assert (Forall2 (fun x => IStr.sem_var_instant (CIStr.tr_history H n) (fst x)) (ins ++ outs)
                    (map (fun x => tr_Stream x n) (vins ++ vouts))) as Ho.
    { rewrite Forall2_map_2. eapply Forall2_impl_In; [|eapply Ho1]. intros (?&?&?) ? ? ? ?.
      eapply CIStr.sem_var_impl in H2; eauto. } clear Ho1.
    assert (Forall2 (fun x => IStr.sem_var_instant (CIStr.tr_history H' n) (fst x)) (ins ++ outs)
                    (map (fun x => tr_Stream x n) (vins ++ vouts))) as Ho'.
    { rewrite Forall2_map_2. eapply Forall2_impl_In; [|eapply Ho2]. intros (?&?&?) ? ? ? ?.
      eapply CIStr.sem_var_impl in H2; eauto. } clear Ho2.
    assert (Forall (fun '(x, _) => forall v, IStr.sem_var_instant (CIStr.tr_history H n) x v -> IStr.sem_var_instant (CIStr.tr_history H' n) x v)
                   (map (fun '(x, (_, ck, _)) => (x, ck)) (ins ++ outs))) as Hvars.
    { simpl_Forall.
      eapply Forall2_ignore2 in Ho'. simpl_Forall.
      intros ? Hvar. eapply IStr.sem_var_instant_det in H2; eauto; subst. assumption.
    } clear Ho Ho'.
    rewrite <-map_app in Hin1.

    revert b b0 Hsc.
    induction Hin1; intros; inv Hsc; [eapply IStr.Sbase|eapply IStr.Son|eapply IStr.Son_abs1|eapply IStr.Son_abs2]; eauto.
    - rewrite H5. eapply IHHin1. congruence.
    - simpl_Forall; eauto.
    - rewrite H5. eapply IHHin1. congruence.
    - simpl_Forall; eauto.
    - specialize (IHHin1 b0 (Streams.const true)). rewrite tr_Stream_const in IHHin1; eauto.
    - simpl_Forall; eauto.
  Qed.

  (** First step of the proof:
      Prove that every named stream of the node is aligned with the clock
      of its variable *)
  Section sc_inv.
    Context {PSyn : block -> Prop}.
    Context {prefs : PS.t}.
    Variable (G : @global PSyn prefs).

    Hypothesis Hnode : forall f ins outs,
        sem_node G f ins outs ->
        sem_clock_inputs G f ins ->
        sem_node_ck G f ins outs.

    Lemma Hscnodes :
      forall G1 H f n xs (* vs *) os,
        wc_node G1 n ->
        Sem.sem_node G f xs os ->
        find_node f G = Some n ->
        Forall2 (sem_var H) (idents (n_in n)) xs ->
        Forall2 (sem_var H) (idents (n_out n)) os ->
        Forall2 (fun xc => sem_clock H (clocks_of xs) (snd xc))
                (map (fun '(x, (_, ck, _)) => (x, ck)) (n_in n)) (map abstract_clock xs) ->
        Forall2 (fun xc => sem_clock H (clocks_of xs) (snd xc))
                (map (fun '(x, (_, ck, _)) => (x, ck)) (n_out n)) (map abstract_clock os).
    Proof.
      intros * Hwc Hsem Hfind Hins Houts Hckins.
      eapply Hnode in Hsem. 2:(repeat esplit; eauto).
      destruct Hwc as (_&Hwc&_). inv Hsem.
      rewrite Hfind in H1. inv H1.
      eapply sem_clocks_det; eauto.
      unfold idents in *. simpl_Forall.
      destruct H6 as (_&(?&Hvar&?)&_). 1:econstructor; solve_In; eauto using in_or_app; eauto.
      simpl in *. eapply sem_var_det in H8; eauto.
      rewrite <-H8; auto.
    Qed.

    Definition sc_var_inv Γ (H : Sem.history) (b : Stream bool) : ident -> Prop :=
      fun cx =>
        (forall x ck xs,
            HasCaus Γ x cx ->
            HasClock Γ x ck ->
            sem_var (fst H) x xs ->
            sem_clock (fst H) b ck (abstract_clock xs))
        /\ (forall x ck xs,
              HasLastCaus Γ x cx ->
              HasClock Γ x ck ->
              sem_var (snd H) x xs ->
              sem_clock (fst H) b ck (abstract_clock xs)).

    Lemma sc_vars_sc_var_inv : forall Γ H b,
        sc_vars Γ H b ->
        Forall (sc_var_inv Γ H b) (map snd (idcaus_of_senv Γ)).
    Proof.
      intros * (Hinv1&Hinv2).
      simpl_Forall. split; intros * Hca Hck Hvar.
      - edestruct Hinv1 as (?&Hvar'&?); eauto.
        eapply sem_var_det in Hvar; eauto. now rewrite <-Hvar.
      - edestruct Hinv2 as (?&Hvar'&?); eauto.
        inv Hca; econstructor; eauto. congruence.
        eapply sem_var_det in Hvar; eauto.
        now rewrite <-Hvar.
    Qed.

    Lemma sc_var_inv_sc_vars : forall Γ H b,
        NoDupMembers Γ ->
        (forall x, IsVar Γ x -> exists v, sem_var (fst H) x v) ->
        (forall x, IsLast Γ x -> exists v, sem_var (snd H) x v) ->
        Forall (sc_var_inv Γ H b) (map snd (idcaus_of_senv Γ)) ->
        sc_vars Γ H b.
    Proof.
      intros * Hnd Hv1 Hv2 Hinv.
      unfold idcaus_of_senv in Hinv. rewrite map_app in Hinv.
      apply Forall_app in Hinv as (Hinv1&Hinv2).
      unfold sc_vars. split; intros * Hck; [|intros Hca].
      - inv Hck.
        edestruct Hv1 as (?&Hvar); eauto with senv.
        eapply Forall_forall in Hinv1 as (Hinv1&_). 2:solve_In. simpl in *.
        do 2 esplit; eauto.
        eapply Hinv1; eauto. 1,2:econstructor; solve_In; eauto.
      - inv Hck. inv Hca. eapply NoDupMembers_det in H0; eauto; subst.
        edestruct Hv2 as (?&Hvar).
        1:{ econstructor; eauto. }
        destruct (causl_last _) eqn:Hcaus; try congruence.
        eapply Forall_forall in Hinv2 as (_&Hinv2). 2:solve_In; rewrite Hcaus; simpl; eauto.
        do 2 esplit; eauto.
        eapply Hinv2; eauto. 1,2:econstructor; solve_In; eauto.
    Qed.

    Definition sc_exp_inv Γ Γty H b : exp -> nat -> Prop :=
      fun e k => forall ss,
          wt_exp G Γty e ->
          wc_exp G Γ e ->
          Sem.sem_exp G H b e ss ->
          sem_clock (fst H) b (nth k (clockof e) Cbase) (abstract_clock (nth k ss (def_stream b))).

    Fact P_exps_sc_exp_inv : forall Γ Γty H b es ss k,
        Forall (wt_exp G Γty) es ->
        Forall (wc_exp G Γ) es ->
        Forall2 (Sem.sem_exp G H b) es ss ->
        P_exps (sc_exp_inv Γ Γty H b) es k ->
        sem_clock (fst H) b (nth k (clocksof es) Cbase) (abstract_clock (nth k (concat ss) (def_stream b))).
    Proof.
      induction es; intros * Hwt Hwc Hsem Hp;
        inv Hwt; inv Hwc; inv Hsem; simpl. inv Hp.
      assert (length y = numstreams a) as Hlen by (eapply sem_exp_numstreams; eauto with ltyping).
      inv Hp.
      - (* now *)
        rewrite app_nth1. 2:rewrite length_clockof_numstreams; auto.
        rewrite app_nth1. 2:congruence.
        eapply H10; eauto.
      - (* later *)
        rewrite app_nth2. 1,2:rewrite length_clockof_numstreams; auto.
        rewrite app_nth2. 1,2:rewrite Hlen; auto.
    Qed.

    Fact Forall2Brs_sc_exp_inv1 : forall Γ Γty H b ck x tx es k ss,
        k < length ss ->
        Forall (fun es => Forall (wt_exp G Γty) (snd es)) es ->
        Forall (fun es => Forall (wc_exp G Γ) (snd es)) es ->
        Forall (fun '(i, es0) => Forall (eq (Con ck x (tx, i))) (clocksof es0)) es ->
        Forall (fun es0 => length ss = length (clocksof (snd es0))) es ->
        Forall2Brs (Sem.sem_exp G H b) es ss ->
        Forall (fun es => P_exps (sc_exp_inv Γ Γty H b) (snd es) k) es ->
        Forall (fun '(i, v) => sem_clock (fst H) b (Con ck x (tx, i)) (abstract_clock v)) (nth k ss []).
    Proof.
      induction es; intros * Hlen Hwt Hwc Hck1 Hck2 Hsem Hp;
        inv Hwt; inv Hwc; inv Hck1; inv Hck2; inv Hsem; inv Hp; simpl.
      1:{ eapply Forall_forall in H0; [|eapply nth_In]; eauto.
          rewrite H0; auto. }
      eapply P_exps_sc_exp_inv in H12 as Heq1. 4:eauto. 2-3:eauto.
      eapply IHes in H14 as Heq2. 7:eauto. 2-6:eauto.
      2,3:(eapply Forall3_length in H13 as (Hlen1&Hlen2); rewrite Hlen2; auto).
      clear - Hlen H6 H8 H13 Heq1 Heq2.
      eapply Forall3_forall3 in H13 as (?&?&?).
      erewrite H2 at 1; try reflexivity. 2:congruence.
      constructor; eauto; simpl in *.
      eapply Forall_forall in H6; [|eapply nth_In; setoid_rewrite <-H8; eauto].
      erewrite <-H6 in Heq1; eauto.
    Qed.

    Fact P_exps_sc_exp_inv_all : forall Γ Γty H b es ss,
        Forall (wt_exp G Γty) es ->
        Forall (wc_exp G Γ) es ->
        Forall2 (Sem.sem_exp G H b) es ss ->
        (forall k, k < length (annots es) -> P_exps (sc_exp_inv Γ Γty H b) es k) ->
        Forall2 (sem_clock (fst H) b) (clocksof es) (map abstract_clock (concat ss)).
    Proof.
      intros * Hwt Hwc Hsem Hk.
      assert (length (clocksof es) = length (concat ss)) as Hlen.
      { rewrite length_clocksof_annots. symmetry.
        eapply sem_exps_numstreams; eauto with ltyping. }
      eapply Forall2_forall2; split. rewrite map_length; auto.
      intros * Hn ? ?; subst.
      erewrite map_nth' with (d':=def_stream b). 2:congruence.
      erewrite nth_indep with (d':=Cbase); auto.
      eapply P_exps_sc_exp_inv; eauto.
      eapply Hk. rewrite <- length_clocksof_annots; auto.
    Qed.

    Lemma sc_exp_const : forall Γ Γty H b c,
        sc_exp_inv Γ Γty H b (Econst c) 0.
    Proof.
      intros * ? _ Hwc Hsem; inv Hsem.
      simpl. rewrite H4, ac_const.
      constructor. reflexivity.
    Qed.

    Lemma sc_exp_enum : forall Γ Γty H b k ty,
        sc_exp_inv Γ Γty H b (Eenum k ty) 0.
    Proof.
      intros * ? _ Hwc Hsem; inv Hsem.
      simpl. rewrite H6, ac_enum.
      constructor. reflexivity.
    Qed.

    Lemma sc_exp_var : forall Γ Γty H b x cx ann,
        HasCaus Γ x cx ->
        sc_var_inv Γ H b cx ->
        sc_exp_inv Γ Γty H b (Evar x ann) 0.
    Proof.
      intros * (* 1 Hnd2 *) Hin (Hvar&_) ss _ Hwc Hsem; inv Hsem; simpl.
      eapply Hvar; [eauto| |eauto].
      inv Hwc; auto.
    Qed.

    Lemma sc_exp_last : forall Γ Γty H b x cx ann,
        HasLastCaus Γ x cx ->
        sc_var_inv Γ H b cx ->
        sc_exp_inv Γ Γty H b (Elast x ann) 0.
    Proof.
      intros * (* 1 Hnd2 *) Hin (_&Hvar) ss _ Hwc Hsem; inv Hsem; simpl.
      eapply Hvar; [eauto| |eauto].
      inv Hwc; auto.
    Qed.

    Lemma sc_exp_unop : forall Γ Γty H b op e1 ann,
        sc_exp_inv Γ Γty H b e1 0 ->
        sc_exp_inv Γ Γty H b (Eunop op e1 ann) 0.
    Proof.
      intros * He1 ss Hwt Hwc Hsem; inv Hwt; inv Hwc; inv Hsem; simpl.
      eapply He1 in H13; eauto. rewrite H10 in H13; simpl in H13.
      rewrite <- ac_lift1; eauto.
    Qed.

    Lemma sc_exp_binop : forall Γ Γty H b op e1 e2 ann,
        sc_exp_inv Γ Γty H b e1 0 ->
        sc_exp_inv Γ Γty H b e2 0 ->
        sc_exp_inv Γ Γty H b (Ebinop op e1 e2 ann) 0.
    Proof.
      intros * He1 He2 ss Hwt Hwc Hsem; inv Hwt; inv Hwc; inv Hsem; simpl.
      eapply He1 in H16; eauto. rewrite H14 in H16; simpl in H14.
      rewrite <- ac_lift2; eauto.
    Qed.

    Lemma sc_exp_fby : forall Γ Γty H b e0s es ann k,
        k < length ann ->
        P_exps (sc_exp_inv Γ Γty H b) e0s k ->
        sc_exp_inv Γ Γty H b (Efby e0s es ann) k.
    Proof.
      intros * Hk Hexps ss Hwt Hwc Hsem; simpl.
      inv Hwt. inv Hwc. inv Hsem.
      eapply P_exps_sc_exp_inv in Hexps; eauto.
      rewrite Forall2_eq in H10. rewrite H10.
      assert (Forall2 (fun x y => abstract_clock x ≡ abstract_clock y) (concat s0ss) ss).
      { clear - H18. eapply Forall3_ignore2 in H18.
        eapply Forall2_impl_In; eauto.
        intros ? ? _ _ [? ?]. apply ac_fby1 in H; auto. }
      apply Forall2_forall2 in H0 as [_ Hac].
      erewrite <- Hac; eauto.
      erewrite sem_exps_numstreams, <- length_clocksof_annots, <- H10, map_length; eauto with ltyping.
    Qed.

    Lemma sc_exp_arrow : forall Γ Γty H b e0s es ann k,
        k < length ann ->
        P_exps (sc_exp_inv Γ Γty H b) e0s k ->
        P_exps (sc_exp_inv Γ Γty H b) es k ->
        sc_exp_inv Γ Γty H b (Earrow e0s es ann) k.
    Proof.
      intros * Hk He0s Hes ss Hwt Hwc Hsem; simpl.
      inv Hwt. inv Hwc. inv Hsem.
      eapply P_exps_sc_exp_inv in He0s; eauto.
      rewrite Forall2_eq in H10. rewrite H10.
      assert (Forall2 (fun x y => abstract_clock x ≡ abstract_clock y) (concat s0ss) ss).
      { clear - H18. eapply Forall3_ignore2 in H18.
        eapply Forall2_impl_In; eauto.
        intros ? ? _ _ [? ?]. apply ac_arrow1 in H; auto. }
      apply Forall2_forall2 in H0 as [_ Hac].
      erewrite <- Hac; eauto.
      erewrite sem_exps_numstreams, <- length_clocksof_annots, <- H10, map_length; eauto with ltyping.
    Qed.

    Lemma sc_exp_when : forall Γ Γty H b es x tx cx b' ann k,
        NoDupMembers Γ ->
        k < length (fst ann) ->
        P_exps (sc_exp_inv Γ Γty H b) es k ->
        HasCaus Γ x cx ->
        sc_var_inv Γ H b cx ->
        sc_exp_inv Γ Γty H b (Ewhen es (x, tx) b' ann) k.
    Proof.
      intros * Hnd Hk Hes Hin Hvar ss Hwt Hwc Hsem; simpl.
      inv Hwt. inv Hwc. inv Hsem.
      eapply P_exps_sc_exp_inv in Hes; eauto.
      take (sem_var _ _ _) and assert (Hv:=it). eapply Hvar in Hv; eauto.
      erewrite map_nth' with (d':=OpAux.bool_velus_type); eauto.
      eapply Forall_forall in H13. 2:eapply nth_In; rewrite <- H14; eauto.
      eapply sc_when in Hes; eauto. erewrite H13; eauto.
      eapply Forall2_forall2 in H20 as [_ Hwhen].
      eapply Hwhen; eauto.
      replace (length (concat ss0)) with (length (annots es)). rewrite <- length_clocksof_annots, <- H14; eauto.
      symmetry. eapply sem_exps_numstreams; eauto with ltyping.
    Qed.

    Lemma sc_exp_merge : forall Γ Γty H b x cx tx es ann k,
        NoDupMembers Γ ->
        k < length (fst ann) ->
        HasCaus Γ x cx ->
        sc_var_inv Γ H b cx ->
        Forall (fun es => P_exps (sc_exp_inv Γ Γty H b) (snd es) k) es ->
        sc_exp_inv Γ Γty H b (Emerge (x, tx) es ann) k.
    Proof.
      intros * Hnd Hk Hin Hvar Hes ss Hwt Hwc Hsem; simpl.
      inv Hwt. inv Hwc. inv Hsem.
      assert (length vs = length tys) as Hlen1.
      { eapply Forall2Brs_length1 in H21.
        2:{ simpl_Forall. eapply sem_exp_numstreams; eauto with lclocking. }
        destruct es as [|(?&?)]; try congruence. simpl in *.
        inv H21; simpl in *.
        inv H16. rewrite H11, length_clocksof_annots; auto.
      }
      assert (Hlen2:=H21). eapply Forall2Brs_length2 in Hlen2.
      eapply Forall2Brs_sc_exp_inv1 in H21; eauto.
      2,3:rewrite Hlen1; auto.
      eapply Forall2_forall2 in H22 as (Hlen3&Hmerge).
      eapply sc_merge in Hmerge. 1,3:eauto. 4,5:eauto. 3:simpl in *; congruence.
      - eapply Forall_forall in Hlen2; [|eapply nth_In; rewrite Hlen1; eauto].
        instantiate (1:=[]). instantiate (1:=[]) in Hlen2.
        destruct (nth k vs []), es; simpl in *; congruence.
      - eapply Forall_impl; [|eapply H21]; intros (?&?) ?; simpl.
        rewrite map_nth' with (d':=bool_velus_type); eauto.
    Qed.

    Lemma sc_exp_case : forall Γ Γty H b e es d ann k,
        k < length (fst ann) ->
        sc_exp_inv Γ Γty H b e 0 ->
        Forall (fun es => P_exps (sc_exp_inv Γ Γty H b) (snd es) k) es ->
        LiftO True (fun d => P_exps (sc_exp_inv Γ Γty H b) d k) d ->
        sc_exp_inv Γ Γty H b (Ecase e es d ann) k.
    Proof.
      intros * Hk He Hes Hd ss Hwt Hwc Hsem; simpl.
      inv Hwt; inv Hwc; inv Hsem.
      - assert (length vs = length tys) as Hlen1.
        { eapply Forall2Brs_length1 in H26.
          2:{ simpl_Forall. eapply sem_exp_numstreams; eauto with lclocking. }
          destruct es as [|(?&?)]; try congruence. simpl in *.
          inv H26; simpl in *.
          inv H10. rewrite length_typesof_annots; auto.
        }
        eapply Forall3_forall3 in H27 as (?&?&Hcase).
        eapply ac_case in Hcase. rewrite <-Hcase.
        3:instantiate (2:=[]). 4:instantiate (2:=None). 3-5:reflexivity. 2:rewrite Hlen1; auto.
        eapply He in H25; eauto.
        rewrite H14 in H25; simpl in H25.
        erewrite map_nth' with (d':=bool_velus_type); eauto.
      - assert (length vs = length (typesof d0)) as Hlen1.
        { eapply Forall2Brs_length1 in H29.
          2:{ simpl_Forall. eapply sem_exp_numstreams; eauto with lclocking. }
          destruct es as [|(?&?)]; try congruence. simpl in *.
          inv H29; simpl in *.
          inv H11. rewrite <-H13, length_typesof_annots; auto.
        }
        eapply Forall3_forall3 in H31 as (?&?&Hcase).
        eapply ac_case in Hcase. rewrite <-Hcase.
        3:instantiate (2:=[]). 4:instantiate (2:=None). 3-5:reflexivity. 2:rewrite Hlen1; auto.
        eapply He in H24; eauto.
        rewrite H16 in H24; simpl in H24.
        erewrite map_nth' with (d':=bool_velus_type); eauto.
    Qed.

    Lemma sc_exp_app : forall Γ Γty H b f es er ann k,
        wc_global G ->
        k < length ann ->
        (forall k0 : nat, k0 < length (annots es) -> P_exps (sc_exp_inv Γ Γty H b) es k0) ->
        sc_exp_inv Γ Γty H b (Eapp f es er ann) k.
    Proof.
      intros * HwcG Hlen Hk' ? Hwt Hwc Hsem; simpl.

      assert (length ss = length ann0) as Hlen'.
      { eapply sem_exp_numstreams in Hsem; eauto with lclocking. }

      inv Hwt. inv Hwc. inv Hsem.
      eapply wc_find_node in HwcG as (G'&Wcn); eauto.
      assert (Wcn':=Wcn). destruct Wcn' as (WcIn&WcInOut&_).
      rewrite H6 in H13; inv H13.

      (* Arguments *)
      assert (Hse:=H11). eapply P_exps_sc_exp_inv_all in Hse; eauto.

      (* Returning aligned values *)
      assert (Hvars:=H11).
      eapply sem_exps_sem_var, sc_outside_mask with (ncks:=map (fun '(_, ck) => (ck, None)) ann0) in Hvars; eauto.
      - eapply Forall2_forall2 in Hvars as [? Hck].
        repeat rewrite map_length in *.
        specialize (Hck Cbase (abstract_clock (def_stream b)) _ _ _ Hlen eq_refl eq_refl).
        rewrite map_nth, map_map in Hck; eauto.
        erewrite map_ext; eauto. intros (?&?); auto.
      - apply Forall2_map_1, Forall2_forall; split; auto; intros (?&?); simpl; auto.
      - (* Returning aligned values *)
        intros k'.
        specialize (H24 k'). inv H24. rewrite H1 in H6; inv H6.
        exists H0. repeat split; eauto.
        eapply sc_inside_mask in WcIn. 3-5:eauto. 2:eauto.
        eapply Hscnodes in H1; eauto. econstructor; eauto.
    Qed.

    Lemma sc_exp' : forall Γ Γty H b e k,
        NoDupMembers Γ ->
        wc_global G ->
        wt_exp G Γty e ->
        wc_exp G Γ e ->
        k < numstreams e ->
        (forall cx, Is_free_left Γ cx k e -> sc_var_inv Γ H b cx) ->
        sc_exp_inv Γ Γty H b e k.
    Proof.
      intros * Hnd1 Hsc Hwt Hwc Hnum Hfree.
      eapply exp_causal_ind with (Γ:=Γ) (P_exp:=sc_exp_inv _ _ H b); eauto with lclocking; intros.
      - apply sc_exp_const.
      - apply sc_exp_enum.
      - eapply sc_exp_var; eauto.
      - eapply sc_exp_last; eauto.
      - apply sc_exp_unop; auto.
      - apply sc_exp_binop; auto.
      - apply sc_exp_fby; auto.
      - apply sc_exp_arrow; auto.
      - eapply sc_exp_when; eauto.
      - eapply sc_exp_merge; eauto.
      - apply sc_exp_case; auto.
      - eapply sc_exp_app; eauto.
    Qed.

    Lemma sc_exp_equation : forall Γ Γty H b xs es k cx,
        wc_global G ->
        NoDup (map snd (idcaus_of_senv Γ)) ->
        NoDupMembers Γ ->
        k < length xs ->
        wt_equation G Γty (xs, es) ->
        wc_equation G Γ (xs, es) ->
        Sem.sem_equation G H b (xs, es) ->
        (forall cx, Is_free_left_list Γ cx k es -> sc_var_inv Γ H b cx) ->
        HasCaus Γ (nth k xs xH) cx ->
        sc_var_inv Γ H b cx.
    Proof.
      intros * HwcG Hnd1 Hnd2 Hk Hwt Hwc Hsem Hexps Hin. split; intros ???? Hin' Hvar.
      2:{ exfalso. simpl_In.
          eapply NoDup_HasCaus_HasLastCaus; eauto. }
      inv Hwt. inv Hsem.
      assert (x = nth k xs xH).
      { eapply HasCaus_snd_det; eauto. } subst.
      assert (xs0 ≡ nth k (concat ss) (def_stream b)) as Hequiv.
      { eapply Forall2_forall2 in H9 as [_ Hvar'].
        specialize (Hvar' xH (def_stream b) _ _ _ Hk eq_refl eq_refl).
        eapply sem_var_det in Hvar'; eauto. }
      rewrite Hequiv; auto.
      inv Hwc.
      - (* app *)
        assert (nth k (map snd anns) Cbase = ck); subst; auto.
        { eapply Forall2_forall2 in H13 as [_ HIn'].
          specialize (HIn' xH Cbase _ _ _ Hk eq_refl eq_refl).
          inv Hin'. inv HIn'.
          eapply NoDupMembers_det in H3; eauto; subst. auto. }

        simpl_Forall. rename H4 into Hsem.
        assert (length y = length anns) as Hlen'.
        { eapply sem_exp_numstreams in Hsem; eauto with ltyping. }

        inv H14. inv Hsem.
        assert (HwcG':=HwcG). eapply wc_find_node in HwcG' as (G'&Wcn); eauto.
        assert (Wcn':=Wcn). destruct Wcn' as (WcIn&WcInOut&_).
        rewrite H7 in H17; inv H17.

        (* Arguments *)
        assert (Hse:=H24). eapply P_exps_sc_exp_inv_all in Hse; eauto.
        2:{ intros.
            eapply Pexp_Pexps; eauto.
            - simpl_Forall. eapply sc_exp'; eauto.
            - intros ??. eapply Hexps.
              left; simpl. 2:constructor.
              1,2:(apply Forall2_length in H13; setoid_rewrite <-H13; auto).
              left.
              eapply Is_free_left_list_Exists; eauto.
        }

        (* Returning aligned values *)
        simpl in *. rewrite app_nil_r in *.
        assert (Hvars:=H24).
        eapply sem_exps_sem_var, sc_outside_mask with (ncks:=map (fun '(ck, x) => (ck, Some x)) (combine (map snd anns) xs)) in Hvars; eauto.
        + eapply Forall2_forall2 in Hvars as [? Hck].
          repeat rewrite map_length in *.
          assert (k < length (combine (map snd anns) xs)) as Hlen2.
          { apply Forall2_length in H2. rewrite combine_length, H2, 2 map_length, Nat.min_id.
            now erewrite <-map_length, <-H2. }
          specialize (Hck Cbase (abstract_clock (def_stream b)) _ _ _ Hlen2 eq_refl eq_refl).
          erewrite map_nth, map_map, map_ext, combine_map_fst' in Hck; eauto.
          1:eapply Forall2_length in H2; rewrite H2, 2 map_length; eauto.
          intros (?&?); auto.
        + apply Forall2_map_1, Forall3_combine'1, Forall3_ignore1'.
          { apply Forall2_length in H13; auto. rewrite map_length; auto. }
          eapply Forall2_impl_In; [|eauto]; intros; simpl in *; auto.
        + simpl_Forall; eauto.
        + eapply Forall2_map_2, Forall3_combine'2; eauto.
        + (* Returning aligned values *)
          intros k'.
          specialize (H28 k'). inv H28. rewrite H3 in H7; inv H7.
          exists H1. repeat split; eauto.
          eapply sc_inside_mask in WcIn. 3-5:eauto. 2:eauto.
          eapply Hscnodes in Wcn; eauto. econstructor; eauto. simpl_Forall; eauto.
      - assert (nth k (clocksof es) Cbase = ck); subst; auto.
        { eapply Forall2_forall2 in H6 as [_ HIn'].
          specialize (HIn' xH Cbase _ _ _ Hk eq_refl eq_refl).
          inv Hin'. inv HIn'. eapply NoDupMembers_det in H3; eauto; subst. auto.
        }
        assert (P_exps (sc_exp_inv Γ Γty H b) es k) as Hexps'.
        { eapply Pexp_Pexps; eauto.
          - simpl_Forall. eapply sc_exp'; eauto.
          - eapply Forall2_length in H2. rewrite length_typesof_annots in H2. congruence.
        }

        eapply P_exps_sc_exp_inv in Hexps'; eauto.
    Qed.

    (** ** more `mask` properties *)

    Lemma sc_var_inv_mask : forall Γ H b x r k,
        sc_var_inv Γ H b x ->
        sc_var_inv Γ (Sem.mask_hist k r H) (maskb k r b) x.
    Proof.
      intros * Hinv.
      split; intros ???? Hin Hvar;
        [destruct Hinv as (Hinv&_)|destruct Hinv as (_&Hinv)];
        eapply sem_var_mask_inv in Hvar as (?&Hvar&Heq);
        rewrite Heq, ac_mask;
        eapply sem_clock_mask;
        eapply Hinv; eauto.
    Qed.

    Lemma sc_var_inv_unmask : forall Γ H b x r,
      (forall k : nat, sc_var_inv Γ (Sem.mask_hist k r H) (maskb k r b) x) ->
      sc_var_inv Γ H b x.
    Proof.
      intros * Hinv. split; intros ???? Hin Hvar.
      1,2:(eapply sem_clock_unmask with (r:=r); intros k;
           specialize (Hinv k)).
      destruct Hinv as (Hinv&_). 2:destruct Hinv as (_&Hinv).
      1,2:(rewrite <-ac_mask; eapply Hinv; eauto;
           eapply sem_var_mask; eauto).
    Qed.

    Section sem_block_ck'.

      Section sem_scope.

        Context {A : Type}.

        Variable sem_block : static_env -> Sem.history -> A -> Prop.

        Inductive sem_scope_ck' (envS : list ident) : static_env -> Sem.history -> Stream bool -> (scope A) -> Prop :=
        | Sckscope : forall Γ Hi Hi' Hl Hl' bs locs caus blks,
            (forall x vs, sem_var Hi' x vs -> ~InMembers x locs -> sem_var Hi x vs) ->

            FEnv.refines (@EqSt _) Hl Hl' ->
            (forall x ty ck cx e0 clx,
                In (x, (ty, ck, cx, Some (e0, clx))) locs ->
                exists vs0 vs1 vs,
                  sem_exp G (Hi', Hl') bs e0 [vs0] /\ sem_var Hi' x vs1 /\ fby vs0 vs1 vs /\ sem_var Hl' x vs) ->

            sem_block (replace_idcaus caus Γ ++ senv_of_locs locs) (Hi', Hl') blks ->

            Forall (fun x => sc_var_inv (senv_of_locs locs) (Hi + Hi', Hl') bs x) envS ->
            Forall (fun cx => forall x ck vs, In (x, cx) caus -> HasClock Γ x ck -> sem_var Hi x vs -> sem_clock Hi bs ck (abstract_clock vs)) envS ->
            sem_scope_ck' envS Γ (Hi, Hl) bs (Scope locs caus blks).
      End sem_scope.

      Inductive sem_block_ck' (envP : list ident) : static_env -> Sem.history -> Stream bool -> block -> Prop :=
      | Sckbeq : forall Γ Hi bs eq,
          sem_equation G Hi bs eq ->
          sem_block_ck' envP Γ Hi bs (Beq eq)
      | Sckreset : forall Γ Hi bs blocks er sr r,
          sem_exp G Hi bs er [sr] ->
          bools_of sr r ->
          (forall k, Forall (sem_block_ck' envP Γ (Sem.mask_hist k r Hi) (maskb k r bs)) blocks) ->
          sem_block_ck' envP Γ Hi bs (Breset blocks er)
      | Sckswitch:
        forall Γ Hi b ec branches sc,
          sem_exp G Hi b ec [sc] ->
          wt_streams [sc] (typeof ec) ->
          Forall (fun blks =>
                    exists Hi', Sem.filter_hist (fst blks) sc Hi Hi'
                           /\ let bi := ffilterb (fst blks) sc b in
                             sem_scope_ck' (fun Γ Hi' => Forall (sem_block_ck' envP Γ Hi' bi))
                                           envP (map (fun '(x, a) => (x, ann_with_clock a Cbase)) Γ) Hi' bi (snd blks)) branches ->
          sem_block_ck' envP Γ Hi b (Bswitch ec branches)
      | SckautoWeak:
        forall Γ H bs ini oth states ck bs' stres0 stres1 stres,
          sem_clock (fst H) bs ck bs' ->
          sem_transitions G H bs' (List.map (fun '(e, t) => (e, (t, false))) ini) (oth, false) stres0 ->
          fby stres0 stres1 stres ->
          Forall (fun state =>
                    let tag := fst (fst state) in
                    forall k, exists Hik, Sem.select_hist tag k stres H Hik
                                /\ let bik := fselectb tag k stres bs in
                                  sem_scope_ck' (fun Γ Hi' blks =>
                                                   Forall (sem_block_ck' envP Γ Hi' bik) (fst blks)
                                                   /\ sem_transitions G Hi' bik (snd blks) (tag, false) (fselect absent (tag) k stres stres1)
                                                ) envP (map (fun '(x, a) => (x, ann_with_clock a Cbase)) Γ) Hik bik (snd (snd state))
                 ) states ->
          sem_block_ck' envP Γ H bs (Bauto Weak ck (ini, oth) states)
      | SckautoStrong:
        forall Γ H bs ini states ck bs' stres stres1,
          sem_clock (fst H) bs ck bs' ->
          fby (const_stres bs' (ini, false)) stres1 stres ->
          Forall (fun state =>
                    let tag := fst (fst state) in
                    forall k, exists Hik, Sem.select_hist tag k stres H Hik
                                /\ let bik := fselectb tag k stres bs in
                                  sem_transitions G Hik bik (fst (snd state)) (tag, false) (fselect absent (tag) k stres stres1)
                 ) states ->
          Forall (fun state =>
                    let tag := fst (fst state) in
                    forall k, exists Hik, Sem.select_hist tag k stres1 H Hik
                                /\ let bik := fselectb tag k stres1 bs in
                                  sem_scope_ck' (fun Γ Hi' blks => Forall (sem_block_ck' envP Γ Hi' bik) (fst blks)
                                                ) envP (map (fun '(x, a) => (x, ann_with_clock a Cbase)) Γ) Hik bik (snd (snd state))
                 ) states ->
          sem_block_ck' envP Γ H bs (Bauto Strong ck ([], ini) states)
      | Scklocal:
        forall Γ Hi bs scope,
          sem_scope_ck' (fun Γ Hi' => Forall (sem_block_ck' envP Γ Hi' bs)) envP Γ Hi bs scope ->
          sem_block_ck' envP Γ Hi bs (Blocal scope).

      Lemma sem_block_sem_block_ck' : forall blk Γ Hi bs,
          sem_block G Hi bs blk ->
          sem_block_ck' [] Γ Hi bs blk.
      Proof.
        induction blk using block_ind2; intros * Hsem; inv Hsem.
        - (* equation *)
          constructor; auto.
        - (* reset *)
          econstructor; eauto.
          intros k. specialize (H7 k).
          simpl_Forall; eauto.
        - (* switch *)
          econstructor; eauto.
          simpl_Forall; do 2 esplit; eauto.
          inv H3; econstructor; eauto. simpl_Forall; eauto.
        - (* automaton (weak) *)
          econstructor; eauto.
          simpl_Forall. specialize (H10 k); destruct_conjs.
          do 2 esplit; eauto.
          inv H2; econstructor; eauto. destruct_conjs; split; simpl_Forall; eauto.
        - (* automaton (strong) *)
          econstructor; eauto.
          simpl_Forall. specialize (H10 k); destruct_conjs.
          do 2 esplit; eauto.
          inv H2; econstructor; eauto. simpl_Forall; eauto.
        - (* locals *)
          constructor.
          inv H3; econstructor; eauto.
          simpl_Forall; eauto.
      Qed.

      Lemma sem_block_ck'_sem_block : forall envP blk Γ Hi bs,
          sem_block_ck' envP Γ Hi bs blk ->
          sem_block G Hi bs blk.
      Proof.
        induction blk using block_ind2; intros * Hsem; inv Hsem.
        - (* equation *)
          constructor; auto.
        - (* reset *)
          econstructor; eauto.
          intros k. specialize (H7 k).
          simpl_Forall; eauto.
        - (* switch *)
          econstructor; eauto.
          simpl_Forall; do 2 esplit; simpl_Forall; eauto.
          inv H3; econstructor; eauto. simpl_Forall; eauto.
        - (* automaton (weak) *)
          econstructor; eauto.
          simpl_Forall. specialize (H11 k); destruct_conjs.
          do 2 esplit; eauto.
          inv H2; econstructor; eauto. destruct_conjs; split; simpl_Forall; eauto.
        - (* automaton (strong) *)
          econstructor; eauto.
          simpl_Forall. specialize (H11 k); destruct_conjs.
          do 2 esplit; eauto.
          inv H2; econstructor; eauto. simpl_Forall; eauto.
        - (* locals *)
          constructor.
          inv H4. econstructor; eauto.
          simpl_Forall; eauto.
      Qed.

      Lemma sem_block_ck'_Perm : forall xs ys blk Γ Hi bs,
          Permutation xs ys ->
          sem_block_ck' xs Γ Hi bs blk ->
          sem_block_ck' ys Γ Hi bs blk.
      Proof.
        induction blk using block_ind2; intros * Hperm Hsem;
          inv Hsem.
        - (* equation *)
          constructor; auto.
        - (* reset *)
          econstructor; eauto.
          intros k. specialize (H7 k).
          simpl_Forall; eauto.
        - (* switch *)
          econstructor; eauto.
          simpl_Forall; do 2 esplit; eauto.
          inv H3; econstructor; eauto.
          simpl_Forall; eauto.
          1,2:setoid_rewrite <-Hperm; auto.
        - (* automaton (weak) *)
          econstructor; eauto.
          simpl_Forall. specialize (H11 k); destruct_conjs.
          do 2 esplit; eauto. inv H2; destruct_conjs. econstructor; eauto.
          split; simpl_Forall; eauto.
          1,2:setoid_rewrite <-Hperm; auto.
        - (* automaton (strong) *)
          econstructor; eauto.
          simpl_Forall. specialize (H11 k); destruct_conjs.
          do 2 esplit; eauto. inv H2; destruct_conjs. econstructor; eauto.
          simpl_Forall; eauto.
          1,2:setoid_rewrite <-Hperm; auto.
        - (* local *)
          constructor.
          inv H4. econstructor; eauto.
          simpl_Forall; eauto.
          1,2:setoid_rewrite <-Hperm; auto.
      Qed.

      Global Add Parametric Morphism envP Γ : (sem_block_ck' envP Γ)
          with signature (history_equiv ==> eq ==> eq ==> Basics.impl)
            as sem_block_ck'_Equiv.
      Proof.
        intros Hi1 Hi2 HH bs blk. revert Hi1 Hi2 HH bs.
        induction blk using block_ind2; intros * HH * Hsem; inv Hsem.
        - (* equation *)
          constructor. now rewrite <-HH.
        - (* reset *)
          econstructor; eauto.
          + now rewrite <-HH.
          + intros k. specialize (H7 k).
            simpl_Forall; eauto.
            eapply H; eauto.
            destruct HH as (HH1&HH2); split; unfold Sem.mask_hist.
            now rewrite <-HH1. now rewrite <-HH2.
        - (* switch *)
          econstructor; eauto.
          + now rewrite <-HH.
          + simpl_Forall; do 2 esplit; eauto.
            destruct HH as (HH1&HH2), H1. split.
            * now rewrite <-HH1.
            * now rewrite <-HH2.
        - (* automaton (weak) *)
          econstructor; eauto.
          + destruct HH as (HH1&HH2). rewrite <-HH1; eauto.
          + now rewrite <-HH.
          + simpl_Forall. specialize (H11 k); destruct_conjs.
            do 2 esplit; eauto.
            destruct HH as (HH1&HH2), H1. split.
            * now rewrite <-HH1.
            * now rewrite <-HH2.
        - (* automaton (strong) *)
          econstructor; eauto.
          + destruct HH as (HH1&HH2). rewrite <-HH1; eauto.
          + simpl_Forall. specialize (H10 k); destruct_conjs.
            do 2 esplit; eauto.
            destruct HH as (HH1&HH2), H1. split.
            * now rewrite <-HH1.
            * now rewrite <-HH2.
          + simpl_Forall. specialize (H11 k); destruct_conjs.
            do 2 esplit; eauto.
            destruct HH as (HH1&HH2), H1. split.
            * now rewrite <-HH1.
            * now rewrite <-HH2.
        - (* locals *)
          destruct Hi2. constructor.
          inv H4; econstructor. 3,4:eauto.
          + intros. destruct HH as (HH&_). rewrite <-HH. eapply H3; eauto.
          + destruct HH as (_&HH). rewrite <-HH; eauto.
          + simpl_Forall. destruct HH as (HH1&HH2). destruct H11.
            split; simpl in *; intros; rewrite <-FEnv.union_Equiv; eauto; try reflexivity.
            rewrite <-FEnv.union_Equiv in H8; eauto; try reflexivity.
          + simpl_Forall. destruct HH as (HH1&_).
            rewrite <-HH1. eapply H12; eauto. now rewrite HH1.
      Qed.

      Lemma sem_scope_ck'_refines {A} P_vd P_nd P_sem : forall envP locs caus (blk: A) xs Γ H H' Hl bs,
          VarsDefinedScope P_vd (Scope locs caus blk) xs ->
          NoDupScope P_nd xs (Scope locs caus blk) ->
          FEnv.refines (@EqSt _) H H' ->
          sem_scope_ck' P_sem envP Γ (H, Hl) bs (Scope locs caus blk) ->
          (forall xs Γ Γ' Hi Hl,
            incl xs Γ ->
            P_vd blk xs ->
            P_nd Γ blk ->
            P_sem Γ' (Hi, Hl) blk ->
            FEnv.dom_lb Hi xs) ->
          (forall xs Γ Hi Hi' Hl,
              P_vd blk xs ->
              P_nd xs blk ->
              FEnv.refines (@EqSt _) Hi Hi' ->
              P_sem Γ (Hi, Hl) blk ->
              P_sem Γ (Hi', Hl) blk) ->
          sem_scope_ck' P_sem envP Γ (H', Hl) bs (Scope locs caus blk).
      Proof.
        intros * Hvd Hnd Href Hsem Hdoml Hind; inv Hvd; inv Hnd; inv Hsem.
        econstructor; [|eauto|eauto|eauto|eauto|]; eauto using sem_var_refines.
        - assert ((H + Hi') ⊑ (H' + Hi')) as Href'.
          { intros ?? Hfind.
            eapply FEnv.union4' in Hfind as [Hfind1|(Hfind1&Hfind2)].
            - do 2 esplit; eauto using FEnv.union3'. reflexivity.
            - eapply Href in Hfind1 as (vs'&?&?). do 2 esplit; eauto using FEnv.union2.
          }
          simpl_Forall. destruct H17 as (Hsc1&Hsc2); simpl in *.
          split; intros ???? Hin Hv.
          1,2:eapply sem_clock_refines; eauto. eapply Hsc1; eauto; simpl in *.
          assert (FEnv.dom_lb Hi' (map fst locs)) as Hdom.
          { intros ??. eapply Hdoml in H4; eauto using incl_refl.
            apply H4; auto using in_or_app. }
          inv Hin. simpl_In.
          eapply sem_var_refines''; eauto using FEnv.union_dom_lb2.
          solve_In.
        - simpl_Forall. eapply sem_clock_refines, H18; eauto.
          eapply sem_var_refines'; eauto.
          eapply Hdoml in H4; eauto using incl_refl.
          assert (In x0 (xs ++ map fst locs)) as Hin.
          { apply in_app_iff, or_introl, H5. solve_In. }
          apply H4 in Hin as (?&?).
          eapply sem_var_In, H11. econstructor; eauto; reflexivity.
          intros contra. eapply H8; eauto. eapply H5; solve_In.
      Qed.

      Lemma sem_block_ck'_refines : forall envP blk xs Γ H H' Hl bs,
          VarsDefined blk xs ->
          NoDupLocals xs blk ->
          FEnv.refines (@EqSt _) H H' ->
          sem_block_ck' envP Γ (H, Hl) bs blk ->
          sem_block_ck' envP Γ (H', Hl) bs blk.
      Proof.
        induction blk using block_ind2; intros * Hvars Hnd Href Hsem;
          inv Hvars; inv Hnd; inv Hsem.
        - (* equation *)
          constructor; eauto using Sem.sem_equation_refines.
        - (* reset *)
          econstructor; eauto using Sem.sem_exp_refines.
          intros k. specialize (H10 k).
          rewrite Forall_forall in *; intros; eauto.
          eapply Forall2_ignore2, Forall_forall in H4 as (?&?&?); eauto.
          eapply H. 1-3,5:eauto.
          + eapply NoDupLocals_incl; eauto. eapply incl_concat; eauto.
          + eapply FEnv.refines_map; eauto. intros ?? Heq. now rewrite Heq.
        - (* switch *)
          econstructor; eauto using Sem.sem_exp_refines.
          simpl_Forall. do 2 esplit; eauto.
          destruct H2; split; auto.
          intros ?? Hfind. apply H2 in Hfind as (?&Heq1&Hfind). apply Href in Hfind as (?&Heq2&Hfind).
          do 2 esplit; [|eauto]. rewrite <-Heq2; auto.
        - (* automaton (weak) *)
          econstructor; eauto using sem_clock_refines, Sem.sem_transitions_refines.
          simpl_Forall. specialize (H15 k); destruct_conjs.
          do 2 esplit; eauto.
          destruct H2 as (Hsel1&?); split; auto.
          intros ?? Hfind. apply Hsel1 in Hfind as (?&Heq1&Hfind). apply Href in Hfind as (?&Heq2&Hfind).
          do 2 esplit; [|eauto]. rewrite <-Heq2; auto.
        - (* automaton (strong) *)
          econstructor; eauto using sem_clock_refines, Sem.sem_transitions_refines.
          + simpl_Forall. specialize (H14 k); destruct_conjs.
            do 2 esplit; eauto.
            destruct H2 as (Hsel1&?); split; auto.
            intros ?? Hfind. apply Hsel1 in Hfind as (?&Heq1&Hfind). apply Href in Hfind as (?&Heq2&Hfind).
            do 2 esplit; [|eauto]. rewrite <-Heq2; auto.
          + simpl_Forall. specialize (H15 k); destruct_conjs.
            do 2 esplit; eauto.
            destruct H2 as (Hsel1&?); split; auto.
            intros ?? Hfind. apply Hsel1 in Hfind as (?&Heq1&Hfind). apply Href in Hfind as (?&Heq2&Hfind).
            do 2 esplit; [|eauto]. rewrite <-Heq2; auto.
        - (* locals *)
          constructor.
          eapply sem_scope_ck'_refines; eauto.
          1,2:intros; simpl in *; simpl_Forall; inv_VarsDefined; eauto.
          + eapply Forall_sem_block_dom_lb; eauto;
              simpl_Forall; eauto using NoDupLocals_incl, sem_block_ck'_sem_block.
          + eapply H; eauto.
            eapply NoDupLocals_incl; [|eauto]. rewrite <-H9; eauto using incl_concat.
      Qed.

      Corollary sem_scope_ck'_refines1 : forall envP locs caus blk Γ Γ' xs H H' Hl bs,
          incl xs Γ ->
          VarsDefinedScope (fun blks ys => exists xs : list (list ident), Forall2 VarsDefined blks xs /\ Permutation (concat xs) ys) (Scope locs caus blk) xs ->
          NoDupScope (fun Γ => Forall (NoDupLocals Γ)) Γ (Scope locs caus blk) ->
          FEnv.refines (@EqSt _) H H' ->
          sem_scope_ck' (fun Γ Hi => Forall (sem_block_ck' envP Γ Hi bs)) envP Γ' (H, Hl) bs (Scope locs caus blk) ->
          sem_scope_ck' (fun Γ Hi => Forall (sem_block_ck' envP Γ Hi bs)) envP Γ' (H', Hl) bs (Scope locs caus blk).
      Proof.
        intros * Hincl Hdef Hnd Href Hsem.
        eapply sem_scope_ck'_refines; eauto.
        - eapply NoDupScope_incl; eauto.
          intros; simpl in *; simpl_Forall; eauto using NoDupLocals_incl.
        - intros; simpl in *. inv_VarsDefined.
          eapply Forall_sem_block_dom_lb; eauto;
            simpl_Forall; eauto using NoDupLocals_incl, sem_block_ck'_sem_block.
        - intros; simpl in *; simpl_Forall. inv_VarsDefined.
          eapply sem_block_ck'_refines; eauto.
          eapply NoDupLocals_incl; eauto. rewrite <-H5; eauto using incl_concat.
      Qed.

      Corollary sem_scope_ck'_refines2 : forall envP locs caus blk Γ Γ' xs H H' Hl bs def stres,
          incl xs Γ ->
          VarsDefinedScope (fun blks ys => exists xs : list (list ident), Forall2 VarsDefined (fst blks) xs /\ Permutation (concat xs) ys) (Scope locs caus blk) xs ->
          NoDupScope (fun Γ blks => Forall (NoDupLocals Γ) (fst blks)) Γ (Scope locs caus blk) ->
          FEnv.refines (@EqSt _) H H' ->
          sem_scope_ck' (fun Γ Hi blks => Forall (sem_block_ck' envP Γ Hi bs) (fst blks)
                                     /\ sem_transitions G Hi bs (snd blks) def stres) envP Γ' (H, Hl) bs (Scope locs caus blk) ->
          sem_scope_ck' (fun Γ Hi blks => Forall (sem_block_ck' envP Γ Hi bs) (fst blks)
                                     /\ sem_transitions G Hi bs (snd blks) def stres) envP Γ' (H', Hl) bs (Scope locs caus blk).
      Proof.
        intros * Hincl Hdef Hnd Href Hsem.
        eapply sem_scope_ck'_refines; eauto.
        - eapply NoDupScope_incl; eauto.
          intros; simpl in *; simpl_Forall; eauto using NoDupLocals_incl.
        - intros; simpl in *. inv_VarsDefined.
          eapply Forall_sem_block_dom_lb; eauto;
            simpl_Forall; eauto using NoDupLocals_incl, sem_block_ck'_sem_block.
        - intros; simpl in *.
          destruct_conjs; split; eauto using Sem.sem_transitions_refines.
          simpl_Forall. inv_VarsDefined.
          eapply sem_block_ck'_refines; eauto.
          eapply NoDupLocals_incl; eauto. rewrite <-H5; eauto using incl_concat.
      Qed.

      Corollary sem_scope_ck'_refines3 {T} : forall envP locs caus (blk: (list block * T)) Γ Γ' xs H H' Hl bs,
          incl xs Γ ->
          VarsDefinedScope (fun blks ys => exists xs : list (list ident), Forall2 VarsDefined (fst blks) xs /\ Permutation (concat xs) ys) (Scope locs caus blk) xs ->
          NoDupScope (fun Γ blks => Forall (NoDupLocals Γ) (fst blks)) Γ (Scope locs caus blk) ->
          FEnv.refines (@EqSt _) H H' ->
          sem_scope_ck' (fun Γ Hi blks => Forall (sem_block_ck' envP Γ Hi bs) (fst blks)) envP Γ' (H, Hl) bs (Scope locs caus blk) ->
          sem_scope_ck' (fun Γ Hi blks => Forall (sem_block_ck' envP Γ Hi bs) (fst blks)) envP Γ' (H', Hl) bs (Scope locs caus blk).
      Proof.
        intros * Hincl Hdef Hnd Href Hsem.
        eapply sem_scope_ck'_refines; eauto.
        - eapply NoDupScope_incl; eauto.
          intros; simpl in *; simpl_Forall; eauto using NoDupLocals_incl.
        - intros; simpl in *. inv_VarsDefined.
          eapply Forall_sem_block_dom_lb; eauto;
            simpl_Forall; eauto using NoDupLocals_incl, sem_block_ck'_sem_block.
        - intros; simpl in *.
          simpl_Forall. inv_VarsDefined.
          eapply sem_block_ck'_refines; eauto.
          eapply NoDupLocals_incl; eauto. rewrite <-H5; eauto using incl_concat.
      Qed.

      Lemma sem_scope_ck'_restrict {A} P_vd P_nd P_wc sem_block:
        forall envP Γ Γ' xs Hi Hl bs locs caus (blks : A),
          Forall (fun '(_, a) => wc_clock (idck Γ) a.(clo)) Γ' ->
          VarsDefinedScope P_vd (Scope locs caus blks) xs ->
          NoDupScope P_nd xs (Scope locs caus blks) ->
          wc_scope P_wc G Γ (Scope locs caus blks) ->
          sem_scope_ck' sem_block envP Γ' (Hi, Hl) bs (Scope locs caus blks) ->
          (forall xs Γ Γ' Hi,
              incl xs Γ ->
              P_vd blks xs ->
              P_nd Γ blks ->
              sem_block Γ' Hi blks ->
              FEnv.dom_lb (fst Hi) xs) ->
          (forall Γ Γ' xs Hi Hl,
              Forall (fun '(_, a) => wc_clock (idck Γ) a.(clo)) Γ' ->
              P_vd blks xs ->
              P_nd xs blks ->
              P_wc Γ blks ->
              sem_block Γ' (Hi, Hl) blks ->
              sem_block Γ' (FEnv.restrict Hi (List.map fst Γ), Hl) blks) ->
          sem_scope_ck' sem_block envP Γ' (FEnv.restrict Hi (List.map fst Γ), Hl) bs (Scope locs caus blks).
      Proof.
        intros * Hwenv Hvd Hnd Hwc Hsem Hdomlb Hind; inv Hvd; inv Hnd; inv Hwc; inv Hsem.
        eapply Sckscope with (Hi':=FEnv.restrict Hi' (List.map fst (Γ ++ senv_of_locs locs))); eauto.
        - intros * Hsem Hnin.
          eapply sem_var_restrict_inv in Hsem as (Hin&Hsem).
          eapply sem_var_restrict; eauto.
          simpl_app. apply in_app_iff in Hin as [Hin|Hin]; auto.
          setoid_rewrite map_fst_senv_of_locs in Hin.
          exfalso. apply Hnin, fst_InMembers; auto.
        - intros * Hin. edestruct H17; eauto. destruct_conjs.
          simpl_Forall.
          do 3 esplit. repeat split; eauto.
          eapply Sem.sem_exp_restrict; eauto with lclocking.
          eapply sem_var_restrict; eauto. simpl_app. apply in_or_app. right. solve_In.
        - eapply Hind; eauto.
          apply Forall_app; split; simpl_Forall; simpl_In; simpl_Forall.
          + simpl_app. eapply wc_clock_incl; [|destruct (assoc_ident _ _); eauto]. solve_incl_app.
          + simpl_app. simpl_In. simpl_Forall. auto.
        - rewrite Forall_forall in *. intros * Hinp.
          assert (FEnv.dom_lb Hi' (map fst locs)) as Hdom2.
          { eapply FEnv.dom_lb_incl. 2:eapply Hdomlb with (xs:=xs++_) in H18; eauto using incl_refl.
            intros ??; auto using in_or_app. }
          assert (FEnv.refines (@EqSt _)
                              ((FEnv.restrict Hi (map fst Γ)) + (FEnv.restrict Hi' (map fst (Γ ++ senv_of_locs locs))))
                              (Hi + Hi')) as Href.
          { intros ?? Hfind.
            eapply FEnv.union4' in Hfind as [Hfind1|(Hfind1&Hfind2)].
            - eapply FEnv.restrict_find_inv in Hfind1 as (?&?).
              exists v. split; try reflexivity; eauto using FEnv.union3'.
            - eapply FEnv.restrict_find_inv in Hfind1 as (Hin'&Hfind1).
              exists v. split; try reflexivity. eapply FEnv.union2; eauto.
              apply FEnv.restrict_find_None_inv in Hfind2 as [|Hnin]; auto.
              exfalso. apply Hnin. simpl_app; auto using in_or_app.
          }
          assert (forall x vs,
                     IsVar (Γ ++ senv_of_locs locs) x ->
                     sem_var (Hi + Hi') x vs ->
                     sem_var ((FEnv.restrict Hi (map fst Γ)) + (FEnv.restrict Hi' (map fst (Γ ++ senv_of_locs locs)))) x vs) as Href'.
          { intros ?? Hinm Hvar'. inv Hvar'.
            eapply FEnv.union4' in H0 as [Hfind1|(Hfind1&Hfind2)].
            - econstructor; eauto. eapply FEnv.union3', FEnv.restrict_find; eauto.
              apply fst_InMembers. now inv Hinm.
            - inv Hinm. apply InMembers_app in H as [Hinm|Hinm].
              + econstructor; eauto.
                eapply FEnv.union2; eauto using FEnv.restrict_find_None2.
                eapply FEnv.restrict_find; eauto. now apply fst_InMembers.
              + apply InMembers_senv_of_locs, fst_InMembers, Hdom2 in Hinm as (?&?).
                congruence.
          }
          split; intros ???? Hin Hvar; simpl in *.
          + edestruct H19 as (Hv&_); eauto. eapply sem_var_refines, Hv in Hvar; eauto.
            eapply sem_clock_refines'; [| |eauto]; eauto.
            * inv Hin. eapply wc_clock_wx_clock in H10; eauto. solve_In.
          + edestruct H19 as (_&Hv); eauto. eapply Hv in Hvar; eauto.
            eapply sem_clock_refines'; [| |eauto]; eauto.
            * inv Hin. eapply wc_clock_wx_clock in H10; eauto. solve_In.
        - simpl_Forall.
          eapply sem_var_restrict_inv in H5 as (?&?).
          eapply sem_clock_refines'; [| |eauto]; eauto.
          + inv H1. simpl_Forall; eauto with lclocking.
          + intros. apply sem_var_restrict; [|auto]. inv H14.
            now apply fst_InMembers.
      Qed.

      Lemma sem_block_ck'_restrict : forall envP blk xs Γ Γ' H Hl bs,
          Forall (fun '(_, a) => wc_clock (idck Γ) a.(clo)) Γ' ->
          VarsDefined blk xs ->
          NoDupLocals xs blk ->
          wc_block G Γ blk ->
          sem_block_ck' envP Γ' (H, Hl) bs blk ->
          sem_block_ck' envP Γ' (FEnv.restrict H (List.map fst Γ), Hl) bs blk.
      Proof with eauto with lclocking.
        induction blk using block_ind2; intros * Hwenv Hvars Hnd Hwc Hsem;
          inv Hvars; inv Hnd; inv Hwc; inv Hsem.

        - (* equation *)
          econstructor.
          eapply Sem.sem_equation_restrict...

        - (* reset *)
          econstructor; eauto.
          + eapply Sem.sem_exp_restrict...
          + intros k; specialize (H13 k). simpl_Forall.
            eapply Forall2_ignore2, Forall_forall in H4 as (?&?&?); eauto.
            eapply sem_block_ck'_Equiv; try eapply H; eauto.
            2:{ eapply NoDupLocals_incl; eauto. apply incl_concat; auto. }
            unfold Sem.mask_hist; simpl. split; try reflexivity. now setoid_rewrite <-FEnv.restrict_map.

        - (* switch *)
          econstructor; eauto.
          + eapply Sem.sem_exp_restrict...
          + simpl_Forall. do 2 esplit.
            2:{ destruct s. eapply sem_scope_ck'_restrict; eauto.
                - simpl_Forall. constructor.
                - intros; simpl in *. destruct_conjs. destruct Hi.
                  eapply Forall_sem_block_dom_lb; eauto.
                  + simpl_Forall; eauto using NoDupLocals_incl.
                  + simpl_Forall; eauto using sem_block_ck'_sem_block.
                - intros; simpl in *. destruct_conjs.
                  simpl_Forall. inv_VarsDefined. eapply H; eauto.
                  eapply NoDupLocals_incl; eauto.
                  take (Permutation _ _) and rewrite <-it. apply incl_concat; auto. }
            destruct H2. split; auto.
            simpl. intros ?? Hfind. apply FEnv.restrict_find_inv in Hfind as (Hin&Hfind).
            apply H2 in Hfind as (?&Hfilter&Hfind). do 2 esplit; [eauto|eapply FEnv.restrict_find; eauto].
            simpl_In. edestruct H9 as (Hck&_). 1:econstructor; solve_In; eauto.
            inv Hck. solve_In.

        - (* automaton (weak) *)
          econstructor; eauto.
          + eapply Sem.sem_clock_restrict...
          + eapply Sem.sem_transitions_restrict... simpl_Forall.
            eapply wx_exp_incl with (Γ:=Γ'0); eauto with lclocking.
            intros * Hv. inv Hv. apply fst_InMembers in H5; simpl_In.
            edestruct H11 as (?&?); eauto with senv.
          + simpl_Forall. specialize (H22 k); destruct_conjs.
            do 2 esplit.
            2:{ destruct s. eapply sem_scope_ck'_restrict; eauto.
                - simpl_Forall. constructor.
                - intros; simpl in *. destruct_conjs. destruct Hi.
                  eapply Forall_sem_block_dom_lb; eauto.
                  + simpl_Forall; eauto using NoDupLocals_incl.
                  + simpl_Forall; eauto using sem_block_ck'_sem_block.
                - intros; simpl in *. destruct_conjs.
                  split.
                  + simpl_Forall. inv_VarsDefined. eapply H; eauto.
                    eapply NoDupLocals_incl; eauto.
                    take (Permutation _ _) and rewrite <-it. apply incl_concat; auto.
                  + eapply Sem.sem_transitions_restrict... simpl_Forall; eauto with lclocking. }
            destruct H5 as (Href1&Href2). split; auto.
            intros ?? Hfind. apply FEnv.restrict_find_inv in Hfind as (Hin&Hfind).
            eapply Href1 in Hfind as (?&Hfilter&Hfind').
            do 2 esplit; eauto. apply FEnv.restrict_find; auto.
            simpl_In. edestruct H11 as (?&?); eauto with senv. inv H5. solve_In.

        - (* automaton (strong) *)
          econstructor; eauto.
          + eapply Sem.sem_clock_restrict...
          + simpl_Forall. specialize (H21 k); destruct_conjs.
            do 2 esplit.
            2:{ eapply Sem.sem_transitions_restrict; [|eauto].
                simpl_Forall; eauto with lclocking. }
            destruct H5 as (Href1&Href2). split; auto.
            intros ?? Hfind. apply FEnv.restrict_find_inv in Hfind as (Hin&Hfind).
            eapply Href1 in Hfind as (?&Hfilter&Hfind').
            do 2 esplit; eauto. apply FEnv.restrict_find; auto.
            simpl_In. edestruct H11 as (?&?); eauto with senv. inv H5. solve_In.
          + simpl_Forall. specialize (H22 k); destruct_conjs.
            do 2 esplit.
            2:{ destruct s. eapply sem_scope_ck'_restrict; eauto.
                - simpl_Forall. constructor.
                - intros; simpl in *. destruct_conjs. destruct Hi.
                  eapply Forall_sem_block_dom_lb; eauto.
                  + simpl_Forall; eauto using NoDupLocals_incl.
                  + simpl_Forall; eauto using sem_block_ck'_sem_block.
                - intros; simpl in *. destruct_conjs.
                  simpl_Forall. inv_VarsDefined. eapply H; eauto.
                  eapply NoDupLocals_incl; eauto.
                  take (Permutation _ _) and rewrite <-it. apply incl_concat; auto. }
            destruct H5 as (Href1&Href2). split; auto.
            intros ?? Hfind. apply FEnv.restrict_find_inv in Hfind as (Hin&Hfind).
            eapply Href1 in Hfind as (?&Hfilter&Hfind').
            do 2 esplit; eauto. apply FEnv.restrict_find; auto.
            simpl_In. edestruct H11 as (?&?); eauto with senv. inv H5. solve_In.

        - (* locals *)
          constructor.
          eapply sem_scope_ck'_restrict; eauto.
          + intros; simpl in *. destruct_conjs. destruct Hi.
            eapply Forall_sem_block_dom_lb; eauto.
            * simpl_Forall; eauto using NoDupLocals_incl.
            * simpl_Forall; eauto using sem_block_ck'_sem_block.
          + intros; simpl in *. destruct_conjs.
            simpl_Forall. inv_VarsDefined. eapply H; eauto.
            eapply NoDupLocals_incl; eauto.
            take (Permutation _ _) and rewrite <-it. apply incl_concat; auto.
      Qed.
    End sem_block_ck'.

    Lemma sc_var_inv_unfilter : forall Γ Γ' tx tn sc Hi bs x,
        0 < length tn ->
        wt_stream sc (Tenum tx tn) ->
        (forall y ck, HasCaus Γ y x -> HasClock Γ y ck -> HasCaus Γ' y x /\ HasClock Γ' y Cbase) ->
        (forall y ck, HasCaus Γ y x -> HasClock Γ y ck -> sem_clock (fst Hi) bs ck (abstract_clock sc)) ->
        (forall c, In c (seq 0 (length tn)) ->
              exists Hi',
                (forall y, HasCaus Γ y x -> FEnv.In y (fst Hi'))
                /\ Sem.filter_hist c sc Hi Hi'
                /\ sc_var_inv Γ' Hi' (ffilterb c sc bs) x) ->
        (forall y, ~HasLastCaus Γ y x) ->
        sc_var_inv Γ Hi bs x.
    Proof.
      intros * Hn Hwt Hwc Hsck Hsc Hnin.
      split; intros ??? Hca Hck Hv.
      - assert (sem_clock (fst Hi) bs ck (abstract_clock sc)) as Hsemck by eauto.
        assert (abstract_clock sc ≡ abstract_clock xs) as Heq; [|rewrite <-Heq; eauto].
        apply ntheq_eqst. intros n.
        rewrite 2 ac_nth.
        apply SForall_forall with (n:=n) in Hwt.
        destruct (sc # n) eqn:Hscn. simpl in *.
        + edestruct Hsc with (c:=0) as ((Hi'&?)&Hin&(Hfilter&_)&(Hsc'&_)). apply in_seq; lia.
          assert (exists vs, sem_var Hi' x0 vs) as (?&Hv').
          { edestruct Hin as (?&?); eauto. do 2 esplit; eauto. reflexivity. }
          eapply sem_var_filter_inv in Hv' as (?&?&Hfilter'); eauto.
          eapply sem_var_det in Hv; eauto. rewrite <-Hv.
          eapply filter_nth with (n:=n) in Hfilter' as [(?&Heq&?)|[(?&?)|(?&?&?)]]; try congruence.
          setoid_rewrite Heq. setoid_rewrite H0; auto.
        + inv Hwt. edestruct Hsc with (c:=v0) as ((Hi'&?)&Hin&(Hfilter&_)&(Hsc'&_)). apply in_seq; lia.
          assert (exists vs, sem_var Hi' x0 vs) as (?&Hv').
          { edestruct Hin as (?&?); eauto. do 2 esplit; eauto. reflexivity. }
          assert (Hvx:=Hv'). eapply sem_var_filter_inv in Hvx as (?&?&Hfilter'); eauto.
          eapply sem_var_det in Hv; eauto. rewrite <-Hv.
          edestruct Hwc as (Hca'&Hck'); eauto. eapply Hsc' in Hv'; eauto.
          eapply sem_clock_equiv in Hsemck. specialize (Hsemck n). rewrite 2 tr_Stream_nth, ac_nth in Hsemck.
          eapply sem_clock_equiv in Hv'. specialize (Hv' n). rewrite 2 tr_Stream_nth, ac_nth, ffilterb_nth in Hv'.
          eapply filter_nth with (n:=n) in Hfilter' as [(?&?&?)|[(Heq1&Heq2)|(Heq1&Heq2&Heq3&Heq4)]]; try congruence.
          * setoid_rewrite Heq1 in Hsemck. apply IStr.sem_clock_instant_true_inv in Hsemck.
            rewrite Hsemck, Heq1, equiv_decb_refl in Hv'. setoid_rewrite Heq2.
            inv Hv'. setoid_rewrite Heq1; auto.
      - exfalso. eapply Hnin; eauto.
    Qed.

    Lemma sc_var_inv_unselect : forall Γ Γ' tn sc Hi bs x,
        0 < tn ->
        SForall (fun v => match v with present (e, _) => e < tn | _ => True end) sc ->
        (forall y ck, HasCaus Γ y x -> HasClock Γ y ck -> HasCaus Γ' y x /\ HasClock Γ' y Cbase) ->
        (forall y ck, HasCaus Γ y x -> HasClock Γ y ck -> sem_clock (fst Hi) bs ck (abstract_clock sc)) ->
        (forall c k, In c (seq 0 tn) ->
                exists Hi',
                  (forall y, HasCaus Γ y x -> FEnv.In y (fst Hi'))
                  /\ Sem.select_hist c k sc Hi Hi'
                  /\ sc_var_inv Γ' Hi' (fselectb c k sc bs) x) ->
        (forall y, ~HasLastCaus Γ y x) ->
        sc_var_inv Γ Hi bs x.
    Proof.
      intros * Hn Hwt Hwc Hsck Hsc Hnin.
      split; intros ??? Hca Hck Hv.
      - assert (sem_clock (fst Hi) bs ck (abstract_clock sc)) as Hsemck by eauto.
        assert (abstract_clock sc ≡ abstract_clock xs) as Heq; [|rewrite <-Heq; eauto].
        apply ntheq_eqst. intros n.
        rewrite 2 ac_nth.
        apply SForall_forall with (n:=n) in Hwt.
        destruct (sc # n) as [|(?&?)] eqn:Hscn. simpl in *.
        + edestruct Hsc with (c:=0) as ((Hi'&?)&Hin&(Hfilter&_)&(Hsc'&_)). apply in_seq; lia.
          assert (exists vs, sem_var Hi' x0 vs) as (?&Hv').
          { edestruct Hin as (?&?); eauto. do 2 esplit; eauto. reflexivity. }
          eapply sem_var_select_inv with (k:=(count (ffilterb 0 (stres_st sc) (stres_res sc))) # n) in Hv' as (?&?&Hfilter'); eauto.
          eapply sem_var_det in Hv; eauto. rewrite <-Hv.
          apply select_mask_filter in Hfilter' as (?&Hfil&Hmask).
          eapply filter_nth with (n:=n) in Hfil as [(?&Hx&?)|[(Hscn'&Hx)|(?&Hscn'&?&Hy)]]; try rewrite Hx; auto.
          1,2:setoid_rewrite Str_nth_map in Hscn'; setoid_rewrite Hscn in Hscn'; congruence.
        + edestruct Hsc with (c:=n0) as ((Hi'&?)&Hin&(Hfilter&_)&(Hsc'&_)). apply in_seq; lia.
          assert (exists vs, sem_var Hi' x0 vs) as (?&Hv').
          { edestruct Hin as (?&?); eauto. do 2 esplit; eauto. reflexivity. }
          assert (Hvx:=Hv'). eapply sem_var_select_inv with (k:=(count (ffilterb n0 (stres_st sc) (stres_res sc))) # n) in Hvx as (?&?&Hfilter'); eauto.
          eapply sem_var_det in Hv; eauto. rewrite <-Hv.
          edestruct Hwc as (Hca'&Hck'); eauto. eapply Hsc' in Hv'; eauto.
          eapply sem_clock_equiv in Hsemck. specialize (Hsemck n). rewrite 2 tr_Stream_nth, ac_nth in Hsemck.
          eapply sem_clock_equiv in Hv'. specialize (Hv' n).
          unfold fselectb, fselect in Hv'. rewrite 2 tr_Stream_nth, ac_nth, mask_nth, Nat.eqb_refl, ffilter_nth in Hv'.
          setoid_rewrite Str_nth_map in Hv'. setoid_rewrite Hscn in Hv'. rewrite equiv_decb_refl in Hv'. inv Hv'.
          apply select_mask_filter in Hfilter' as (ys&Hfil&Hmask).
          apply eqst_ntheq with (n:=n) in Hmask. rewrite mask_nth, Nat.eqb_refl in Hmask.
          eapply filter_nth with (n:=n) in Hfil as [(Hscn'&Hx&Hy)|[(Hscn'&Hx)|(?&Hscn'&?&?)]].
          1,3:setoid_rewrite Str_nth_map in Hscn'; setoid_rewrite Hscn in Hscn'; congruence.
          rewrite Hx. rewrite Hscn in Hsemck. apply IStr.sem_clock_instant_true_inv in Hsemck.
          rewrite Hmask in H0. destruct (ys # n); try congruence.
      - exfalso. eapply Hnin; eauto.
    Qed.

    Lemma sc_var_inv_local :
      forall Γ (locs : list (ident * (type * clock * ident * option (exp * ident)))) caus Hi Hl Hi' Hl' bs cx,
        (forall x, InMembers x locs -> ~In x (map fst Γ)) ->
        Forall (fun x => wc_clock (idck (Γ ++ senv_of_locs locs)) (snd x)) (map (fun '(x, (_, ck, _, _)) => (x, ck)) locs) ->
        (forall x, IsLast Γ x -> FEnv.In x Hl) ->
        (forall x vs, sem_var Hi' x vs -> ~ InMembers x locs -> sem_var Hi x vs) ->
        FEnv.refines (EqSt (A:=svalue)) Hl Hl' ->
        FEnv.refines (EqSt (A:=svalue)) Hi (Hi + (FEnv.restrict Hi' (map fst (Γ ++ senv_of_locs locs)))) ->
        (forall x, HasCaus Γ x cx \/ HasLastCaus Γ x cx -> sc_var_inv Γ (Hi, Hl) bs cx) ->
        (forall x, HasCaus (senv_of_locs locs) x cx \/ HasLastCaus (senv_of_locs locs) x cx ->
         sc_var_inv (senv_of_locs locs) (Hi + Hi', Hl') bs cx) ->
        (forall x ck vs, In (x, cx) caus -> HasClock Γ x ck -> sem_var Hi x vs ->
                    sem_clock Hi bs ck (abstract_clock vs)) ->
        sc_var_inv
          (replace_idcaus caus Γ ++ senv_of_locs locs)
          (Hi + (FEnv.restrict Hi' (map fst (Γ ++ senv_of_locs locs))), Hl') bs cx.
    Proof.
      intros * Hnd Hwc Hdom2 Href1 Href2 Href3 Hsc1 Hsc2 Hsc3.
      split; intros ??? Hca Hck Hv;
        rewrite HasClock_app in Hck; (rewrite HasCaus_app in Hca||rewrite HasLastCaus_app in Hca);
        destruct Hck as [Hck|Hck]; try rewrite replace_idcaus_HasClock in Hck.
      - destruct Hca as [Hca|Hca].
        2:{ exfalso. inv Hca. inv Hck. simpl_In.
            eapply Hnd; eauto using In_InMembers. solve_In. }
        eapply sem_clock_refines; [eapply Href3|].
        assert (sem_var Hi x xs) as Hv'.
        { apply sem_var_union in Hv as [Hv|Hv]; auto.
          apply sem_var_restrict_inv in Hv as (Hin&Hv).
          rewrite map_app, map_fst_senv_of_locs, in_app_iff in Hin. destruct Hin as [Hin|Hin].
          - eapply Href1; eauto. intro contra. eapply Hnd; eauto using In_InMembers.
          - exfalso. eapply Hnd. apply fst_InMembers; eauto.
            inv Hca. solve_In.
        }
        apply replace_idcaus_HasCaus3 in Hca as [Hca|Hca].
        + edestruct Hsc1 as (Hinv&_); eauto.
        + simpl in *. eapply Hsc3; eauto.
      - destruct Hca as [Hca|Hca].
        1:{ exfalso. inv Hca. inv Hck. simpl_In.
            eapply Hnd; eauto using In_InMembers. solve_In. }
        edestruct Hsc2 as (Hinv&_); eauto.
        eapply sem_clock_refines', Hinv; eauto.
        + inv Hck; simpl_In. eapply Forall_forall, wc_clock_wx_clock in Hwc; eauto.
          2:solve_In. eauto.
        + intros ?? Hin' Hv'. inv Hv'.
          { eapply FEnv.union4' in H0 as [Hfind1|(Hfind1&Hfind2)].
            - econstructor; eauto.
              eapply FEnv.union3', FEnv.restrict_find; eauto.
              inv Hin'. now apply fst_InMembers.
            - econstructor; eauto.
              eapply FEnv.union2; eauto using FEnv.restrict_find_None2.
          }
        + eapply sem_var_refines; [|eauto]. intros ?? Hfind.
          { eapply FEnv.union4' in Hfind as [Hfind1|(Hfind1&Hfind2)].
            - eapply FEnv.restrict_find_inv in Hfind1 as (?&?).
              do 2 esplit; try reflexivity.
              eapply FEnv.union3'; eauto.
            - destruct (Hi' x0) eqn:Hfind3.
              + assert (v ≡ s).
                { eapply sem_var_det with (H:=Hi). econstructor; eauto; reflexivity.
                  eapply Href1; eauto. econstructor; eauto; reflexivity.
                  intro contra. eapply FEnv.restrict_find_None_inv in Hfind2 as [|Hnin]; try congruence.
                  apply Hnin. apply fst_InMembers.
                  rewrite InMembers_app, InMembers_senv_of_locs; auto. }
               do 2 esplit; eauto. eapply FEnv.union3'; eauto.
              + do 2 esplit; try reflexivity.
                eapply FEnv.union2; eauto.
          }
      - destruct Hca as [Hca|Hca].
        2:{ exfalso. inv Hca. inv Hck. simpl_In.
            eapply Hnd; eauto using In_InMembers. solve_In. }
        rewrite replace_idcaus_HasLastCaus in Hca.
        eapply sem_clock_refines; [eapply Href3|].
        edestruct Hsc1 as (_&Hinv); eauto.
        eapply Hinv; eauto. solve_In.
        eapply sem_var_refines'; [|eauto|eauto].
        eapply Hdom2. inv Hca. econstructor; eauto. congruence.
      - destruct Hca as [Hca|Hca].
        1:{ exfalso. inv Hca. inv Hck. simpl_In.
            eapply Hnd; eauto using In_InMembers. solve_In. }
        edestruct Hsc2 as (_&Hinv); eauto.
        eapply sem_clock_refines', Hinv; eauto.
        + inv Hck; simpl_In. take (Forall (fun _ => wc_clock _ _) _) and eapply Forall_forall in it; eauto.
          2:solve_In. simpl in *. eapply wc_clock_wx_clock in it; eauto.
        + intros ?? Hin' Hv'. inv Hv'.
          { eapply FEnv.union4' in H0 as [Hfind1|(Hfind1&Hfind2)].
            - econstructor; eauto.
              eapply FEnv.union3', FEnv.restrict_find; eauto.
              inv Hin'. now apply fst_InMembers.
            - econstructor; eauto.
              eapply FEnv.union2; eauto using FEnv.restrict_find_None2.
          }
    Qed.

    Lemma sc_transitions' Γty Γ : forall Hi bs' trans def stres,
        wc_global G ->
        NoDupMembers Γ ->
        Forall (fun '(e, _) => wt_exp G Γty e) trans ->
        Forall (fun '(e, _) => wc_exp G Γ e /\ clockof e = [Cbase]) trans ->
        (forall cx, Exists (fun '(e, _) => Is_free_left Γ cx 0 e) trans -> sc_var_inv Γ Hi bs' cx) ->
        sem_transitions G Hi bs' trans def stres ->
        abstract_clock stres ≡ bs'.
    Proof.
      induction trans; intros * HwG Hnd Hwt Hwc Hsc Hsem;
        inv Hwt; inv Hwc; inv Hsem; destruct_conjs.
      - rewrite H0, const_stres_ac. reflexivity.
      - rewrite H13. apply choose_first_ac; eauto.
        eapply sc_exp' with (k:=0) in H6; eauto.
        2:{ rewrite <-length_clockof_numstreams. take (clockof _ = _) and rewrite it; auto. }
        take (clockof _ = _) and rewrite it in H6. simpl in *.
        eapply sc_slower in H6; eauto using ac_aligned.
        apply slower_nth; intros * Hbs. setoid_rewrite Str_nth_map.
        apply slower_nth with (n:=n) in H6; auto.
        apply bools_of_nth with (n:=n) in H7 as [(Hv&Hx)|[(Hv&Hx)|(?&Hx)]].
        + setoid_rewrite H6 in Hv; congruence.
        + setoid_rewrite H6 in Hv; congruence.
        + rewrite Hx; auto.
    Qed.

    Lemma sc_var_inv_subclock Γ Γ' : forall Hi bs bs' cx ck,
        sem_clock (fst Hi) bs ck bs' ->
        (forall x ck', HasClock Γ' x ck' -> HasClock Γ x ck /\ ck' = Cbase) ->
        (forall x, HasCaus Γ' x cx -> HasCaus Γ x cx) ->
        (forall x, HasLastCaus Γ' x cx -> HasLastCaus Γ x cx) ->
        sc_var_inv Γ Hi bs cx ->
        sc_var_inv Γ' Hi bs' cx.
    Proof.
      intros * Hsemck Hck Hca Hlca (Hinv1&Hinv2).
      split; intros * Hasca Hasck Hv.
      - edestruct Hck as (Hasck'&?); eauto; subst.
        eapply Hinv1 in Hv; eauto.
        eapply sem_clock_det in Hsemck; eauto. constructor; symmetry; auto.
      - edestruct Hck as (Hasck'&?); eauto; subst.
        eapply Hinv2 in Hv; eauto.
        eapply sem_clock_det in Hsemck; eauto. constructor; symmetry; auto.
    Qed.

    Lemma sc_scope {A} f_idcaus P_nd P_vd P_wt P_wc (P_blk1 P_blk2 : _ -> _ -> _ -> Prop) P_dep :
      forall envS locs caus (blks: A) Γ Γty xs Hi bs cy,
        wc_global G ->
        NoDup (map snd (idcaus_of_senv Γ ++ idcaus_of_scope f_idcaus (Scope locs caus blks))) ->
        NoDupMembers Γ ->
        NoDupScope P_nd (map fst Γ) (Scope locs caus blks) ->
        VarsDefinedScope P_vd (Scope locs caus blks) xs ->
        incl xs (map fst Γ) ->
        wt_scope P_wt G Γty (Scope locs caus blks) ->
        wc_env (idck Γ) ->
        wc_scope P_wc G Γ (Scope locs caus blks) ->
        sem_scope_ck' P_blk1 envS Γ Hi bs (Scope locs caus blks) ->
        FEnv.dom_ub (fst Hi) (map fst Γ) ->
        (forall x, IsLast Γ x -> FEnv.In x (snd Hi)) ->
        (forall x cx, HasCaus Γ x cx \/ HasLastCaus Γ x cx ->
                 depends_on_scope P_dep Γ cy cx (Scope locs caus blks) -> sc_var_inv Γ Hi bs cx) ->
        (forall cx, In cx (map snd (idcaus_of_scope f_idcaus (Scope locs caus blks))) ->
               depends_on_scope P_dep Γ cy cx (Scope locs caus blks) -> In cx envS) ->
        (forall Γ Γ' xs Hi Hi' Hl,
            P_vd blks xs ->
            P_nd Γ blks ->
            incl xs Γ ->
            FEnv.refines (@EqSt _) Hi Hi' -> P_blk1 Γ' (Hi, Hl) blks -> P_blk1 Γ' (Hi', Hl) blks) ->
        (forall Γ xs Hi Hl,
            wc_env (idck Γ) ->
            P_vd blks xs ->
            P_nd (map fst Γ) blks ->
            incl xs (map fst Γ) ->
            P_wc Γ blks ->
            P_blk1 Γ (Hi, Hl) blks -> P_blk1 Γ (FEnv.restrict Hi (map fst Γ), Hl) blks) ->
        (forall Γ Γ',
            (forall x ck, HasClock Γ x ck -> HasClock Γ' x ck) ->
            (forall x, IsLast Γ x -> IsLast Γ' x) ->
            P_wc Γ blks -> P_wc Γ' blks) ->
        (forall Γ Γty xs Hi,
            NoDup (map snd (idcaus_of_senv Γ ++ f_idcaus blks)) ->
            NoDupMembers Γ ->
            P_nd (map fst Γ) blks ->
            P_vd blks xs ->
            incl xs (map fst Γ) ->
            P_wt Γty blks ->
            wc_env (idck Γ) ->
            P_wc Γ blks ->
            P_blk1 Γ Hi blks ->
            FEnv.dom_ub (fst Hi) (map fst Γ) ->
            (forall x, IsLast Γ x -> FEnv.In x (snd Hi)) ->
            (forall x cx, HasCaus Γ x cx \/ HasLastCaus Γ x cx ->
                     P_dep Γ cy cx blks -> sc_var_inv Γ Hi bs cx) ->
            (forall cx, In cx (map snd (f_idcaus blks)) ->
                   P_dep Γ cy cx blks -> In cx envS) ->
            (forall y, In y xs -> HasCaus Γ y cy -> sc_var_inv Γ Hi bs cy)
            /\ P_blk2 Γ Hi blks) ->
        (forall y, In y xs -> HasCaus Γ y cy -> sc_var_inv Γ Hi bs cy)
        /\ sem_scope_ck' P_blk2 (cy::envS) Γ Hi bs (Scope locs caus blks).
    Proof.
      intros * HwcG Hnd1 Hnd2 Hnd4 Hvars Hincl Hwt Henv Hwc Hsem Hdom Hdoml Hsc HenvP Href Hres Hwcincl Hind;
        inv Hnd4; inv Hvars; inv Hwt; inv Hwc; inv Hsem; simpl in *.

      assert (FEnv.refines (EqSt (A:=svalue)) Hi0
                          (Hi0 + (FEnv.restrict Hi' (map fst (Γ ++ senv_of_locs locs))))) as Href2.
      { intros ?? Hfind. destruct ((FEnv.restrict Hi' (map fst (Γ ++ senv_of_locs locs))) x) eqn:Hfind'.
        - exists s. split; eauto using FEnv.union3'.
          eapply sem_var_det; [now econstructor; try eapply Hfind|].
          eapply H3; eauto.
          + eapply sem_var_restrict_inv. now econstructor; eauto.
          + intros contra. eapply H5; eauto.
            apply Hdom. econstructor; eauto.
        - exists v. split; try reflexivity.
          eapply FEnv.union2; eauto. }

      assert (forall x cx,
                 HasCaus (replace_idcaus caus Γ ++ senv_of_locs locs) x cx
                 \/ HasLastCaus (replace_idcaus caus Γ ++ senv_of_locs locs) x cx ->
                 depends_on_scope P_dep Γ cy cx (Scope locs caus blks) ->
                 sc_var_inv (replace_idcaus caus Γ ++ senv_of_locs locs) (Hi0 + (FEnv.restrict Hi' (map fst (Γ ++ senv_of_locs locs))), Hl') bs cx
             ) as Hscloc.
      { intros * _ Hdep. eapply sc_var_inv_local; eauto.
        - simpl_Forall; auto.
        - intros * Hca. apply idcaus_of_senv_In in Hca.
          eapply Forall_forall in H22; eauto. eapply HenvP; eauto.
          rewrite map_app, in_app_iff. left. solve_In.
        - intros * Hin Hck Hv. simpl_Forall.
          eapply Forall_forall in H23; eauto.
          eapply HenvP; eauto.
          repeat rewrite map_app, in_app_iff. right; left; solve_In.
      }
      assert (forall x ck, HasClock (Γ ++ senv_of_locs locs) x ck ->
                      HasClock (replace_idcaus caus Γ ++ senv_of_locs locs) x ck) as Hckincl.
      { intros *. rewrite 2 HasClock_app, replace_idcaus_HasClock; intros [|]; auto. }
      assert (forall x, IsLast (Γ ++ senv_of_locs locs) x ->
                   IsLast (replace_idcaus caus Γ ++ senv_of_locs locs) x) as Hlincl.
      { intros *. rewrite 2 IsLast_app, replace_idcaus_IsLast; intros [|]; auto. }
      assert (wc_env (idck (replace_idcaus caus Γ ++ senv_of_locs locs))) as Hwenv'.
      { simpl_app. apply wc_env_app; auto.
        - unfold wc_env in *. simpl_Forall.
          erewrite map_map, map_ext. destruct (assoc_ident i caus); eauto.
          intros; destruct_conjs; destruct (assoc_ident _ _); auto.
        - simpl_Forall. erewrite map_map, map_ext; eauto.
          intros; destruct_conjs; destruct (assoc_ident _ _); auto. }

      edestruct Hind with (Hi:=(Hi0 + (FEnv.restrict Hi' (map fst (Γ ++ senv_of_locs locs))), Hl'))
                          (Γ:=replace_idcaus caus Γ ++ senv_of_locs locs) as (Hsc'&Hcons); eauto using in_or_app.
      1:{ rewrite idcaus_of_senv_app, <-app_assoc.
          apply replace_idcaus_NoDup; auto.
          eapply Permutation_NoDup; [|eauto]. solve_Permutation_app. }
      1:{ apply NoDupMembers_app; auto.
          - apply nodupmembers_map; auto.
          - now apply NoDupMembers_senv_of_locs.
          - intros. rewrite InMembers_senv_of_locs. intros ?.
            eapply H5, fst_InMembers; eauto. rewrite fst_InMembers in *. solve_In. }
      1:{ now rewrite map_app, map_fst_senv_of_locs, map_fst_replace_idcaus. }
      1:{ rewrite map_app, map_fst_senv_of_locs, map_fst_replace_idcaus.
          apply incl_appl'; auto. }
      1:{ eapply Href, Hres; eauto. 2-4:rewrite map_app, map_fst_replace_idcaus, <-map_app; auto.
          3,4:rewrite map_app, map_fst_senv_of_locs; auto.
          1,3:apply incl_appl'; auto.
          apply FEnv.union_refines4'; auto using EqStrel_Reflexive. }
      1:{ simpl. rewrite 2 map_app, map_fst_replace_idcaus, map_fst_senv_of_locs.
          apply FEnv.union_dom_ub; auto using FEnv.restrict_dom_ub.
          eapply FEnv.dom_ub_incl; [|eauto]. solve_incl_app.
      }
      1:{ intros * Hin. apply IsLast_app in Hin. rewrite replace_idcaus_IsLast in Hin.
          destruct Hin as [|Hin]; simpl_In; subst.
          + eapply FEnv.In_refines; eauto with senv.
          + inv Hin. simpl_In. destruct o as [(?&?)|]; simpl in *; try congruence.
            edestruct H17 as (?&?&?&?&?&?&?); eauto using sem_var_In. }
      1:{ intros. eapply Hscloc; eauto. econstructor; eauto. }
      1:{ intros. eapply HenvP. 2:econstructor; eauto.
          repeat rewrite map_app, in_app_iff; auto. }
      split.
      - intros * Hinxs Hca.
        split; intros ??? Hca' Hck Hv; simpl_In.
        + eapply HasCaus_snd_det in Hca; eauto; subst. 2:solve_NoDup_app.
          destruct (InMembers_dec y caus ident_eq_dec).
          * apply fst_InMembers in i; simpl_In.
            eapply Forall_forall in H23; eauto. eapply HenvP; eauto using DepOnScope3.
            repeat rewrite map_app, in_app_iff. right; left; solve_In.
          * edestruct Hsc' as (Hsc1&_); eauto using in_or_app.
            apply HasCaus_app; auto using replace_idcaus_HasCaus2.
            eapply sem_var_refines, Hsc1 in Hv; eauto using in_or_app.
            2:rewrite HasCaus_app; auto using replace_idcaus_HasCaus2.
            2:rewrite HasClock_app, replace_idcaus_HasClock; eauto.
            eapply sem_clock_refines_iff; eauto.
            intros * Hfree.
            eapply wc_clock_is_free_in in Hfree; [|eauto].
            2:{ eapply wc_env_var in Henv; eauto. inv Hck; solve_In. }
            apply InMembers_In in Hfree as (?&?); solve_In.
            intros Henvin. apply FEnv.union_In in Henvin as [Henvin|Henvin]; auto.
            apply FEnv.restrict_In in Henvin as (Henvin&_).
            inv Henvin. assert (sem_var Hi' x x1) as Hsemv by (econstructor; eauto; reflexivity).
            apply H3 in Hsemv. inv Hsemv; econstructor; eauto.
            intro contra. eapply H5; eauto; solve_In.
        + exfalso. eapply NoDup_HasCaus_HasLastCaus; eauto. solve_NoDup_app.

      - econstructor. 4:eauto. all:eauto.
        + intros * Hv Hnin.
          apply sem_var_union in Hv as [Hvar|Hvar]; auto.
          apply sem_var_restrict_inv in Hvar as (?&?); eauto.
        + intros. edestruct H17; eauto; destruct_conjs.
          do 3 esplit. repeat split; eauto.
          * simpl_Forall.
            eapply Sem.sem_exp_refines, Sem.sem_exp_restrict; eauto with lclocking.
            rewrite map_app, map_fst_senv_of_locs. apply FEnv.union_refines4'; auto using EqStrel_Reflexive.
          * eapply sem_var_refines, sem_var_restrict; eauto. apply FEnv.union_refines4'; auto using EqStrel_Reflexive.
            simpl_app. apply in_app_iff, or_intror; solve_In.
        + constructor.
          2:{ simpl_Forall. take (sc_var_inv _ _ _ _) and destruct it as (Hsc1&Hsc2).
              assert (forall x vs,
                         IsVar (Γ ++ senv_of_locs locs) x ->
                         sem_var (Hi0 + Hi') x vs ->
                         sem_var (Hi0 + (Hi0 + (FEnv.restrict Hi' (map fst (Γ ++ senv_of_locs locs))))) x vs) as Hvs.
              { intros ?? Hin' Hv'. inv Hv'.
                eapply FEnv.union4' in H1 as [Hind1|(Hfind1&Hfind2)].
                - econstructor; eauto.
                  eapply FEnv.union3', FEnv.union3', FEnv.restrict_find; eauto.
                  inv Hin'. rewrite fst_InMembers in H0; auto.
                - econstructor; eauto.
                  eapply FEnv.union3', FEnv.union2; eauto using FEnv.restrict_find_None2.
              }

              split; intros * Hca Hck Hv; simpl in *; inv Hck; inv Hca; simpl_In; eapply NoDupMembers_det in Hin0; eauto; inv_equalities.
              1,2:eapply Forall_forall in H14 as Hck; [|solve_In; eauto]; simpl in *.
              1,2:eapply sem_clock_refines'; eauto with lclocking.
              - eapply Hsc1; eauto. 1,2:econstructor; solve_In; auto.
                inv Hv. take (_ = Some _) and rename it into Hfind1.
                repeat eapply FEnv.union4' in Hfind1 as [Hfind1|(Hfind1&Hfind2)]; econstructor; eauto.
                + apply FEnv.restrict_find_inv in Hfind1 as (?&?); auto using FEnv.union3'.
                + eapply FEnv.union2; eauto.
                  apply FEnv.restrict_find_None_inv in Hfind2 as [|Hnin]; auto.
                  exfalso. apply Hnin. simpl_app; apply in_or_app, or_intror; solve_In.
                + eapply FEnv.union2; eauto.
                  apply FEnv.union_None in Hfind2 as (_&Hfind2).
                  apply FEnv.restrict_find_None_inv in Hfind2 as [|Hnin]; auto.
                  exfalso. apply Hnin. simpl_app; apply in_or_app, or_intror; solve_In.
              - eapply Hsc2; eauto. 1,2:econstructor; solve_In; auto.
          }
          split; intros * Hca Hck Hv.
          * (* locs *)
            edestruct Hsc' as (Hsc1&_). 2:apply HasCaus_app; eauto.
            1:apply in_or_app, or_intror; inv Hca; solve_In.
            eapply sem_clock_refines, Hsc1; eauto. 2:apply HasCaus_app; eauto. 2:apply HasClock_app; eauto.
            apply FEnv.union_refines4'; auto using EqStrel_Reflexive.
            apply sem_var_union in Hv as [Hv|]; auto. simpl in *.
            eapply sem_var_refines; eauto.

          * (* lasts *)
            inv Hca. inv Hck. simpl_In. eapply NoDupMembers_det in Hin0; eauto; inv Hin0.
            simpl_Forall.
            edestruct H17 as (?&?&?&He&Hv1&Hfby&Hv2); eauto.
            eapply sem_var_det in Hv; eauto. rewrite <-Hv.
            { eapply Sem.sem_exp_restrict, Sem.sem_exp_refines, sc_exp' with (Γ:=replace_idcaus caus Γ++senv_of_locs locs) (k:=0) in He; eauto with lclocking; simpl in *.
              - take (clockof e = _) and setoid_rewrite it in He; simpl in He.
                apply ac_fby1 in Hfby. rewrite <-Hfby.
                eapply sem_clock_refines; eauto.
                eapply FEnv.union_refines4', EqStrel.
              - apply NoDupMembers_app; auto.
                + apply nodupmembers_map; auto.
                + apply NoDupMembers_senv_of_locs; auto.
                + intros. rewrite InMembers_senv_of_locs. intros ?.
                  eapply H5, fst_InMembers; eauto. rewrite fst_InMembers in *; solve_In.
              - eapply wc_exp_incl; eauto.
              - rewrite <-length_clockof_numstreams, H0; auto.
              - intros ? Hfree. edestruct Is_free_left_In_snd; eauto.
                eapply Hscloc; eauto.
                eapply DepOnScope2; eauto. solve_Exists.
              - eapply wc_exp_incl; eauto.
              - rewrite map_app, map_fst_senv_of_locs; auto.
                apply FEnv.union_refines4'; auto using EqStrel_Reflexive.
            }
        + constructor; auto.
          intros * Hcaus Hck Hv.
          edestruct Hsc' as (Hsc1&_). 3:eapply sem_clock_refines', Hsc1; eauto.
          * apply in_app_iff, or_introl, H8; solve_In.
          * apply HasCaus_app. left. inv Hck. eapply replace_idcaus_HasCaus1; eauto with senv.
          * inv Hck. eapply Forall_forall in Henv; [|solve_In]; eauto with lclocking.
          * intros * Hiv' Hv'. eapply sem_var_union in Hv' as [Hv'|Hv']; auto.
            apply sem_var_restrict_inv in Hv' as (_&Hv').
            eapply H3; eauto. intro contra. inv Hiv'. eapply H5; eauto. now apply fst_InMembers.
          * apply HasCaus_app. left. inv Hck. eapply replace_idcaus_HasCaus1; eauto with senv.
          * rewrite HasClock_app, replace_idcaus_HasClock; auto.
          * simpl. eapply sem_var_refines; eauto.
    Qed.

    Lemma sc_block : forall envP blk xs Γ Γty Hi bs cy,
        wc_global G ->
        NoDup (map snd (idcaus_of_senv Γ ++ idcaus_of_locals blk)) ->
        NoDupMembers Γ ->
        NoDupLocals (map fst Γ) blk ->
        VarsDefined blk xs ->
        incl xs (map fst Γ) ->
        wt_block G Γty blk ->
        wc_env (idck Γ) ->
        wc_block G Γ blk ->
        sem_block_ck' envP Γ Hi bs blk ->
        FEnv.dom_ub (fst Hi) (map fst Γ) ->
        (forall x, IsLast Γ x -> FEnv.In x (snd Hi)) ->
        (forall x cx, HasCaus Γ x cx \/ HasLastCaus Γ x cx -> depends_on Γ cy cx blk -> sc_var_inv Γ Hi bs cx) ->
        (forall cx, In cx (map snd (idcaus_of_locals blk)) -> depends_on Γ cy cx blk -> In cx envP) ->
        (forall y, In y xs -> HasCaus Γ y cy -> sc_var_inv Γ Hi bs cy)
        /\ sem_block_ck' (cy::envP) Γ Hi bs blk.
    Proof.
      induction blk as [(xs&es)| | | |] using block_ind2;
        intros * HwG Hnd1 Hnd2 Hnd4 Hvars Hincl Hwt Henv Hwc Hsem Hdom Hdoml Hsc HenvP;
        inv Hnd4; inv Hvars; inv Hwt; inv Hwc; inv Hsem; simpl in *.

      - (* equation *)
        split; [|constructor; auto].
        intros * Hinxs Hca.
        eapply In_nth with (d:=xH) in Hinxs as (?&Hlen&Hnth); subst.
        eapply sc_exp_equation in H5; rewrite app_nil_r in *; eauto.
        intros * Hfree.
        assert (Hfree':=Hfree). eapply Is_free_left_list_In_snd in Hfree as (?&?); eauto.
        eapply Hsc; eauto.
        econstructor; eauto.
        eapply nth_error_nth'; eauto.

      - (* reset *)
        assert (forall k, Forall (fun blks => (forall y xs, VarsDefined blks xs -> In y xs -> HasCaus Γ y cy ->
                                               sc_var_inv Γ (Sem.mask_hist k r Hi) (maskb k r bs) cy)
                                      /\ sem_block_ck' (cy::envP) Γ (Sem.mask_hist k r Hi) (maskb k r bs) blks) blocks) as Hf.
        { intros *. specialize (H15 k). simpl_Forall. inv_VarsDefined.
          edestruct H with (xs:=xs). 10:eauto. all:eauto.
          - clear - H0 Hnd1. eapply NoDup_locals_inv; eauto.
          - etransitivity; eauto using incl_concat.
          - unfold Sem.mask_hist. eapply FEnv.dom_ub_map in Hdom; eauto.
          - setoid_rewrite FEnv.map_in_iff; eauto.
          - intros * Hin' Hdep. eapply sc_var_inv_mask; eauto.
            eapply Hsc; eauto. constructor; solve_Exists.
          - intros * Hin' Hdep. eapply HenvP; eauto. solve_In.
            constructor; solve_Exists.
          - split; eauto.
            intros * HDef' Hin' Hca. eapply H1; eauto.
            eapply VarsDefined_det in Hdef; eauto. now rewrite <-Hdef.
        }
        split.
        + intros * Hinxs Hca.
          apply in_concat in Hinxs as (?&Hin1&Hin2). inv_VarsDefined. simpl_Forall.
          eapply sc_var_inv_unmask; intros.
          specialize (Hf k). simpl_Forall; eauto.
        + econstructor; eauto.
          intros k. specialize (Hf k). simpl_Forall; eauto.

      - (* switch *)
        assert (Is_defined_in Γ cy (Bswitch ec branches) \/ Is_last_in cy (Bswitch ec branches) ->
                sem_clock (fst Hi) bs ck (abstract_clock sc)) as Hsemck.
        { intros.
          assert (Hsem:=H15). eapply sc_exp' with (Γ:=Γ) (k:=0) in Hsem; eauto.
          2:{ rewrite <-length_clockof_numstreams, H12; auto. }
          2:{ intros ? Hfree. assert (Hfree':=Hfree). apply Is_free_left_In_snd in Hfree' as (?&?).
              eapply Hsc; eauto.
              eapply DepOnSwitch2; eauto.
          }
          take (clockof _ = [_]) and rewrite it in Hsem; simpl in *; auto.
        }

        assert (Forall (fun '(k, s) => exists Hi',
                            Sem.filter_hist k sc Hi Hi'
                            /\ (forall y, In y xs -> HasCaus (map (fun '(x, e) => (x, ann_with_clock e Cbase)) Γ) y cy -> sc_var_inv (map (fun '(x, e) => (x, ann_with_clock e Cbase)) Γ) Hi' (ffilterb k sc bs) cy) /\
                              sem_scope_ck'
                                (fun Γ Hi => Forall (sem_block_ck' (cy::envP) Γ Hi (ffilterb k sc bs)))
                                (cy :: envP) (map (fun '(x, a) => (x, ann_with_clock a Cbase)) Γ) Hi' (ffilterb k sc bs) s)
                       branches) as Hf.
        { simpl_Forall. do 2 esplit; eauto.
          destruct s. eapply sc_scope
                        with (P_dep:=fun Γ cx cy => Exists (depends_on Γ cx cy))
                             (Γ:=map (fun '(x, e) => (x, ann_with_clock e Cbase)) Γ) in H18 as (Hsc'&?); eauto.
          - clear - H0 Hnd1.
            eapply NoDup_locals_inv2; eauto.
            unfold idcaus_of_senv in *. erewrite map_map, map_filter_map, map_ext with (l:=Γ), map_filter_ext with (xs:=Γ); eauto.
            1,2:intros; destruct_conjs; auto.
          - apply nodupmembers_map; auto.
          - erewrite map_map, map_ext; eauto. intros; destruct_conjs; auto.
          - erewrite map_map, map_ext; eauto. intros; destruct_conjs; auto.
          - apply Forall_forall; intros ? Hin. simpl_In. constructor.
          - eapply wc_scope_incl; [| |eauto|].
            + intros * Has. eapply H14 in Has as (Has&?).
              inv Has. econstructor; solve_In. auto.
            + intros * His. eapply H16 in His.
              inv His. econstructor; solve_In. auto.
            + intros; simpl in *; simpl_Forall; eauto using wc_block_incl.
          - destruct H1 as (Href&_). eapply FEnv.dom_ub_refines; eauto.
            erewrite map_map, map_ext; eauto. intros; destruct_conjs; auto.
          - intros ? His. destruct H1 as (_&Heq). rewrite Heq. setoid_rewrite FEnv.map_in_iff.
            eapply Hdoml. inv His; simpl_In. econstructor; eauto.
          - intros * ? Hdep.
            assert (forall x, HasCaus Γ x cx \/ HasLastCaus Γ x cx -> In x (map fst Γ')) as Hgamma.
            { intros * Has. eapply depends_scope_In with (Γ':=Γ') (x:=x0) in Hdep; eauto with lclocking.
              - inv Hdep. rewrite <-fst_InMembers; eauto.
              - apply nodupmembers_map; auto.
              - clear - H0 Hnd1.
                eapply NoDup_locals_inv2; eauto. auto.
                unfold idcaus_of_senv in *. simpl_app.
                erewrite map_map with (l:=Γ), map_ext with (l:=Γ), map_filter_map, map_filter_ext; eauto.
                1,2:intros; destruct_conjs; auto.
              - intros ? Hin. eapply VarsDefinedScope_Is_defined with (P_def:=Exists (Syn.Is_defined_in a)) in H5; eauto.
                2:eapply NoDupScope_incl; eauto. 2:intros; simpl in *; simpl_Forall; eauto using NoDupLocals_incl.
                + eapply wc_scope_Is_defined_in, fst_InMembers in H5; eauto.
                  intros; simpl_Exists; simpl_Forall; eauto using wc_block_Is_defined_in.
                + intros; inv_VarsDefined. rewrite <-Hperm in H23. apply in_concat in H23 as (?&Hin1&Hin2).
                  inv_VarsDefined; simpl_Forall. solve_Exists. eapply VarsDefined_Is_defined; eauto.
                  eapply NoDupLocals_incl; [|eauto]. rewrite <-Hperm; eauto using incl_concat.
              - destruct Has as [Has|Has]; inv Has; [left|right]; econstructor; solve_In; auto.
              - erewrite map_map, map_ext; eauto. intros; destruct_conjs; auto.
              - eapply wc_scope_wx_scope; eauto.
              - intros; simpl in *. simpl_Exists; inv_VarsDefined; simpl_Forall.
                eapply depends_on_In with (xs:=xs1); eauto using NoDup_locals_inv with lclocking.
                etransitivity; [|eauto]. rewrite <-H29; eauto using incl_concat.
            }
            assert (forall x ck', HasCaus Γ x cx \/ HasLastCaus Γ x cx -> HasClock Γ x ck' -> ck' = ck) as Hgamma2.
            { intros * Hing Hck. apply Hgamma in Hing. simpl_In.
              edestruct H14 as (Hck'&?); eauto. econstructor; solve_In; eauto.
              inv Hck. inv Hck'. eapply NoDupMembers_det in H22; eauto. congruence. }
            split; intros ??? Hca Hck Hv; inv Hca; inv Hck; simpl_In.
            1,2:eapply NoDupMembers_det in Hin0; eauto; subst.
            1,2:assert (a0.(clo) = ck) by (eapply Hgamma2; eauto with senv); subst.
            + destruct H1 as (Hfilter&_). eapply sem_var_filter_inv in Hv as (?&Hv&Heq); eauto.
              apply filter_ffilter in Heq. rewrite Heq, ac_ffilter.
              assert (depends_on Γ cy (causl a0) (Bswitch ec branches)) as Hdep2.
              { eapply depends_on_incl. 3:econstructor; solve_Exists.
                1,2:intros * Has; inv Has; simpl_In; eauto with senv. }
              eapply Hsc in Hv. 4,5:eauto with senv. 2,3:eauto with senv.
              eapply sem_clock_det in Hv. 2:eapply Hsemck; eauto using depends_on_def_last. rewrite <-Hv.
              eapply sem_clock_filter; eauto using depends_on_def_last.
            + destruct H1 as (?&Hfilter). rewrite Hfilter in Hv.
              eapply sem_var_ffilter_inv in Hv as (?&Hv&Heq). rewrite Heq, ac_ffilter.
              assert (depends_on Γ cy cx (Bswitch ec branches)) as Hdep2.
              { eapply depends_on_incl. 3:econstructor; solve_Exists.
                1,2:intros * Has; inv Has; simpl_In; eauto with senv. }
              eapply Hsc in Hv. 4,5:eauto with senv. 2,3:eauto with senv.
              eapply sem_clock_det in Hv. 2:eapply Hsemck; eauto using depends_on_def_last. rewrite <-Hv.
              eapply sem_clock_filter; eauto using depends_on_def_last.
          - intros ? Hin' Hdep. apply HenvP. solve_In.
            eapply depends_on_incl. 3:econstructor; solve_Exists.
            1,2:intros * Has; inv Has; simpl_In; eauto with senv.
          - intros; simpl in *; simpl_Forall; inv_VarsDefined.
            eapply sem_block_ck'_refines; eauto.
            eapply NoDupLocals_incl; [|eauto]. etransitivity; eauto. rewrite <-H26; eauto using incl_concat.
          - intros; simpl in *; simpl_Forall; inv_VarsDefined.
            eapply sem_block_ck'_restrict; eauto.
            + unfold wc_env, idck in *. simpl_Forall; auto.
            + eapply NoDupLocals_incl; [|eauto]. etransitivity; eauto. rewrite <-H27; eauto using incl_concat.
          - intros; simpl in *; simpl_Forall; eauto using wc_block_incl.
          - intros; simpl in *; simpl_Forall.
            assert (Forall (fun blks => (forall y xs, VarsDefined blks xs -> In y xs -> HasCaus Γ0 y cy ->
                                              sc_var_inv Γ0 Hi0 (ffilterb e sc bs) cy)
                                     /\ sem_block_ck' (cy::envP) Γ0 Hi0 (ffilterb e sc bs) blks) l1) as Hf.
            { simpl_Forall. inv_VarsDefined.
              edestruct H with (Γ:=Γ0) (xs:=xs1). 10:eauto. all:eauto.
              - eapply NoDup_locals_inv; eauto.
              - etransitivity; eauto using incl_concat.
                take (Permutation _ _) and now rewrite it.
              - intros * Hin' Hdep. eapply H31; eauto. solve_Exists.
              - intros * Hin' Hdep. eapply H32; eauto.
                2:solve_Exists. solve_In.
              - split; eauto.
                intros * Hdef' Hin' Hca. eapply H23; eauto.
                eapply VarsDefined_det in Hdef; eauto. now rewrite <-Hdef.
            } clear H.
            split.
            + intros * Hinxs Hca. inv_VarsDefined.
              rewrite <-Hperm in Hinxs. apply in_concat in Hinxs as (?&?&?); inv_VarsDefined; simpl_Forall.
              eapply H33; eauto.
            + simpl_Forall; eauto.
        } clear H H22.
        split.
        + intros * Hinxs Hca1.
          assert (Syn.Is_defined_in y (Bswitch ec branches)) as Hdef.
          { eapply VarsDefined_Is_defined; eauto. econstructor; eauto.
            eapply NoDupLocals_incl; [|econstructor; eauto]. auto. }
          assert (Is_defined_in Γ cy (Bswitch ec branches)) as Hdef' by (eauto using Is_defined_in_Is_defined_in).
          eapply sc_var_inv_unfilter with (tn:=tn) (Γ':=map (fun '(x, e) => (x, ann_with_clock e Cbase)) Γ); eauto.
          * destruct tn; simpl in *; try lia.
            apply Permutation_sym, Permutation_nil, map_eq_nil in H8; congruence.
          * rewrite H6 in H21; inv H21; eauto.
          * intros * Hca Hck.
            eapply HasCaus_snd_det in Hca1; eauto; [|simpl_app; eauto using NoDup_app_l]; subst.
            inv Hck. inv Hca.
            split; econstructor; solve_In; auto.
          * intros * Hca Hck.
            eapply HasCaus_snd_det in Hca1; eauto; [|simpl_app; eauto using NoDup_app_l]; subst.
            inv Hck. inv Hca. eapply NoDupMembers_det in H0; eauto. subst.
            assert (clo e = ck) as Heq; try (rewrite Heq; eauto).
            inv Hdef. rename H18 into Hdef. simpl_Exists; simpl_Forall.
            destruct s. eapply wc_scope_Is_defined_in in Hdef; eauto.
            2:{ intros; simpl_Exists; simpl_Forall; eauto using wc_block_Is_defined_in. }
            eapply InMembers_In in Hdef as (?&Hin').
            edestruct H14 as (Hck&_); eauto with senv.
            inv Hck. eapply NoDupMembers_det in H; eauto. congruence.
          * intros * Hin. rewrite <-H8 in Hin. simpl_In; simpl_Forall.
            do 2 esplit; [|split; eauto].
            1:{ intros ? Hca.
                eapply HasCaus_snd_det in Hca1; eauto; [|simpl_app; eauto using NoDup_app_l]; subst.
                destruct s. eapply sem_scope_defined1; eauto.
                inv H1; econstructor; eauto; simpl_Forall; eauto using sem_block_ck'_sem_block.
            }
            eapply H0; eauto. inv Hca1; econstructor; solve_In. auto.
          * intros * Hnin. eapply NoDup_HasCaus_HasLastCaus; eauto. solve_NoDup_app.
        + econstructor; eauto. simpl_Forall; eauto.

      - (* automaton (weak) *)
        assert (Is_defined_in Γ cy (Bauto Weak ck (ini0, oth) states) \/ Is_last_in cy (Bauto Weak ck (ini0, oth) states) ->
                bs' ≡ abstract_clock stres) as Hac.
        { intros * Hdef.
          symmetry. take (sem_transitions _ _ _ _ _ _) and eapply sc_transitions'
            with (Γ:=map_filter (fun '(x, e) => if e.(clo) ==b ck then Some (x, ann_with_clock e Cbase) else None) Γ) in it; eauto. 3,4:simpl_Forall; eauto.
          - take (fby _ _ _) and apply ac_fby1 in it; now rewrite <-it.
          - apply nodupmembers_map_filter; auto.
            intros; destruct (_ ==b _); simpl; auto.
          - split; auto.
            eapply wc_exp_incl; [| |eauto].
            + intros * Has. eapply H18 in Has as (Has&?).
              inv Has. econstructor. solve_In; simpl. rewrite equiv_decb_refl; eauto.
              auto.
            + intros * His. eapply H19 in His as His'.
              inv His; inv His'. edestruct H18 as (Has&?); eauto with senv.
              inv Has. eapply NoDupMembers_det in H22; eauto; subst.
              econstructor. solve_In; simpl. rewrite equiv_decb_refl; eauto.
              simpl; auto.
          - intros * Hex. simpl_Exists.
            assert (forall x cx, HasCaus (map_filter (fun '(x0, e1) => if clo e1 ==b ck then Some (x0, ann_with_clock e1 Cbase) else None) Γ) x cx -> HasCaus Γ x cx) as Hca.
            { intros * Hca; inv Hca; simpl_In.
              destruct (_ ==b _) eqn:Hck; inv Hf. rewrite equiv_decb_equiv in Hck; inv Hck.
              eauto with senv. }
            assert (forall x cx, HasLastCaus (map_filter (fun '(x0, e1) => if clo e1 ==b ck then Some (x0, ann_with_clock e1 Cbase) else None) Γ) x cx -> HasLastCaus Γ x cx) as Hlca.
            { intros * Hlca; inv Hlca; simpl_In.
              destruct (_ ==b _) eqn:Hck; inv Hf. rewrite equiv_decb_equiv in Hck; inv Hck.
              eauto with senv. }
            eapply sc_var_inv_subclock with (Γ:=Γ); eauto.
            + intros * Hck; inv Hck; simpl_In.
              destruct (_ ==b _) eqn:Hck; inv Hf. rewrite equiv_decb_equiv in Hck; inv Hck.
              eauto with senv.
            + eapply Is_free_left_In_snd in Hex as Hca'. destruct Hca' as (?&Hca').
              eapply Hsc; eauto. destruct Hca'; eauto.
              eapply DepOnAuto3; eauto.
              solve_Exists. eapply Is_free_left_incl in Hex; eauto.
        }
        assert (Forall (fun '((e, _), (_, s)) => forall k, exists Hi',
                            Sem.select_hist e k stres Hi Hi'
                            /\ (forall y, In y xs -> HasCaus (map (fun '(x, e) => (x, ann_with_clock e Cbase)) Γ) y cy ->
                                    sc_var_inv (map (fun '(x, e) => (x, ann_with_clock e Cbase)) Γ) Hi' (fselectb e k stres bs) cy) /\
                              sem_scope_ck'
                                (fun Γ Hi blks => Forall (sem_block_ck' (cy::envP) Γ Hi (fselectb e k stres bs)) (fst blks)
                                             /\ sem_transitions G Hi (fselectb e k stres bs) (snd blks) (e, false) (fselect absent e k stres stres1))
                                (cy :: envP) (map (fun '(x, a) => (x, ann_with_clock a Cbase)) Γ) Hi' (fselectb e k stres bs) s)
                       states) as Hf.
        { simpl_Forall. intros. take (forall (k: nat), _) and specialize (it k); destruct_conjs. destruct s; destruct_conjs.
          do 2 esplit; eauto.
          take (wt_scope _ _ _ _) and eapply sc_scope
            with (P_dep:=fun Γ cx cy blks => Exists (depends_on Γ cx cy) (fst blks))
                 (Γ:=map (fun '(x, e) => (x, ann_with_clock e Cbase)) Γ) in it as (Hsc'&?); eauto.
          - clear - H0 Hnd1.
            eapply NoDup_locals_inv3; eauto.
            unfold idcaus_of_senv in *. erewrite map_map, map_filter_map, map_ext with (l:=Γ), map_filter_ext with (xs:=Γ); eauto.
            1,2:intros; destruct_conjs; auto.
          - apply nodupmembers_map; auto.
          - erewrite map_map, map_ext; eauto. intros; destruct_conjs; auto.
          - erewrite map_map, map_ext; eauto. intros; destruct_conjs; auto.
          - apply Forall_forall; intros ? Hin. simpl_In. constructor.
          - eapply wc_scope_incl; [| |eauto|].
            + intros * Has. eapply H18 in Has as (Has&?).
              inv Has. econstructor; solve_In. auto.
            + intros * His. eapply H19 in His.
              inv His. econstructor; solve_In. auto.
            + intros; simpl in *.
              destruct_conjs; split; eauto; simpl_Forall; eauto using wc_block_incl, wc_exp_incl.
          - take (Sem.select_hist _ _ _ _ _) and destruct it as (Href&_). eapply FEnv.dom_ub_refines; eauto.
            erewrite map_map, map_ext; eauto. intros; destruct_conjs; auto.
          - intros ? His. take (Sem.select_hist _ _ _ _ _) and destruct it as (_&Heq). rewrite Heq. setoid_rewrite FEnv.map_in_iff.
            eapply Hdoml. inv His; simpl_In. econstructor; eauto.
          - intros * ? Hdep.
            assert (forall x, HasCaus Γ x cx \/ HasLastCaus Γ x cx -> In x (map fst Γ')) as Hgamma.
            { intros * Has. eapply depends_scope_In with (Γ':=Γ') (x:=x0) in Hdep; eauto with lclocking.
              - inv Hdep. rewrite <-fst_InMembers; eauto.
              - apply nodupmembers_map; auto.
              - clear - H0 Hnd1.
                eapply NoDup_locals_inv3; eauto. auto.
                unfold idcaus_of_senv in *. simpl_app.
                erewrite map_map with (l:=Γ), map_ext with (l:=Γ), map_filter_map, map_filter_ext; eauto.
                1,2:intros; destruct_conjs; auto.
              - intros ? Hin. eapply VarsDefinedScope_Is_defined with (P_def:=fun blks => Exists (Syn.Is_defined_in a) (fst blks)) in H7; eauto.
                2:eapply NoDupScope_incl; eauto. 2:intros; simpl in *; simpl_Forall; eauto using NoDupLocals_incl.
                + eapply wc_scope_Is_defined_in, fst_InMembers in H7; eauto.
                  intros; simpl_Exists; simpl_Forall; eauto using wc_block_Is_defined_in.
                + intros; inv_VarsDefined. rewrite <-Hperm in H23. apply in_concat in H23 as (?&Hin1&Hin2).
                  inv_VarsDefined; simpl_Forall. solve_Exists. eapply VarsDefined_Is_defined; eauto.
                  eapply NoDupLocals_incl; [|eauto]. rewrite <-Hperm; eauto using incl_concat.
              - destruct Has as [Has|Has]; inv Has; [left|right]; econstructor; solve_In; auto.
              - erewrite map_map, map_ext; eauto. intros; destruct_conjs; auto.
              - eapply wc_scope_wx_scope; eauto.
              - intros; simpl in *. simpl_Exists; inv_VarsDefined; simpl_Forall.
                eapply depends_on_In with (xs:=xs1); eauto using NoDup_locals_inv with lclocking.
                etransitivity; [|eauto]. rewrite <-H33; eauto using incl_concat.
            }
            assert (forall x ck', HasCaus Γ x cx \/ HasLastCaus Γ x cx -> HasClock Γ x ck' -> ck' = ck) as Hgamma2.
            { intros * Hing Hck. apply Hgamma in Hing. simpl_In.
              edestruct H18 as (Hck'&?); eauto. econstructor; solve_In; eauto.
              inv Hck. inv Hck'. eapply NoDupMembers_det in H21; eauto. congruence. }
            split; intros ??? Hca Hck Hv; inv Hca; inv Hck; simpl_In.
            1,2:eapply NoDupMembers_det in Hin0; eauto; subst.
            1,2:assert (a0.(clo) = ck) by (eapply Hgamma2; eauto with senv); subst.
            + take (Sem.select_hist _ _ _ _ _) and destruct it as (Hfilter&_). eapply sem_var_select_inv in Hv as (?&Hv&Heq); eauto.
              apply select_fselect in Heq. rewrite Heq, ac_fselect.
              assert (depends_on Γ cy (causl a0) (Bauto Weak (clo a0) (ini0, oth) states)) as Hdep2.
              { eapply depends_on_incl. 3:econstructor; solve_Exists.
                1,2:intros * Has; inv Has; simpl_In; eauto with senv. }
              eapply Hsc in Hv. 4,5:eauto with senv. 2,3:eauto with senv.
              eapply sem_clock_det in Hv. 2:eapply H24.
              rewrite <-Hv, Hac; eauto using depends_on_def_last.
              eapply sem_clock_select. rewrite <-Hac; eauto using depends_on_def_last.
            + take (Sem.select_hist _ _ _ _ _) and destruct it as (?&Hselect). rewrite Hselect in Hv.
              eapply sem_var_fselect_inv in Hv as (?&Hv&Heq). rewrite Heq, ac_fselect.
              assert (depends_on Γ cy cx (Bauto Weak (clo a0) (ini0, oth) states)) as Hdep2.
              { eapply depends_on_incl. 3:econstructor; solve_Exists.
                1,2:intros * Has; inv Has; simpl_In; eauto with senv. }
              eapply Hsc in Hv. 4,5:eauto with senv. 2,3:eauto with senv.
              eapply sem_clock_det in Hv. 2:eapply H24.
              rewrite <-Hv, Hac; eauto using depends_on_def_last.
              eapply sem_clock_select. rewrite <-Hac; eauto using depends_on_def_last.
          - intros ? Hin' Hdep. apply HenvP. solve_In.
            eapply depends_on_incl. 3:econstructor; solve_Exists.
            1,2:intros * Has; inv Has; simpl_In; eauto with senv.
          - intros; simpl in *; destruct_conjs; split; simpl_Forall; inv_VarsDefined;
              eauto using Sem.sem_transitions_refines.
            eapply sem_block_ck'_refines; eauto.
            eapply NoDupLocals_incl; [|eauto]. etransitivity; eauto. rewrite <-H29; eauto using incl_concat.
          - intros; simpl in *; destruct_conjs; split; simpl_Forall; inv_VarsDefined.
            + eapply sem_block_ck'_restrict; eauto.
              * take (wc_env _) and unfold wc_env, idck in it; simpl_Forall; auto.
              * eapply NoDupLocals_incl; [|eauto]. etransitivity; eauto. rewrite <-H31; eauto using incl_concat.
            + eapply Sem.sem_transitions_restrict; eauto. simpl_Forall; eauto with lclocking.
          - intros; simpl in *; destruct_conjs; split; simpl_Forall; eauto using wc_block_incl, wc_exp_incl.
          - intros; simpl in *. destruct_conjs.
            rewrite <-and_assoc. split; [|auto].
            assert (Forall (fun blks => (forall y xs, VarsDefined blks xs -> In y xs -> HasCaus Γ0 y cy ->
                                              sc_var_inv Γ0 Hi0 (fselectb e k stres bs) cy)
                                     /\ sem_block_ck' (cy::envP) Γ0 Hi0 (fselectb e k stres bs) blks) l2) as Hf.
            { simpl_Forall. inv_VarsDefined.
              edestruct H with (Γ:=Γ0) (xs:=xs1). 10:eauto. all:eauto.
              - eapply NoDup_locals_inv; eauto.
              - etransitivity; eauto using incl_concat.
                take (Permutation _ _) and now rewrite it.
              - intros * Hin' Hdep. eapply H34; eauto. solve_Exists.
              - intros * Hin' Hdep. eapply H35; eauto.
                2:solve_Exists. solve_In.
              - split; eauto.
                intros * Hdef' Hin' Hca. take (forall (y : ident), In _ _ -> _) and eapply it; eauto.
                eapply VarsDefined_det in Hdef; eauto. now rewrite <-Hdef.
            } clear H.
            split.
            + intros * Hinxs Hca. inv_VarsDefined.
              rewrite <-H39 in Hinxs. apply in_concat in Hinxs as (?&?&?); inv_VarsDefined; simpl_Forall.
              take (forall (x : ident) (xs : list ident), _ -> _) and eapply it; eauto.
            + simpl_Forall; eauto.
        } clear H H27.
        split.
        + intros * Hinxs Hca1.
          assert (Syn.Is_defined_in y (Bauto Weak ck (ini0, oth) states)) as Hdef.
          { eapply VarsDefined_Is_defined; eauto. econstructor; eauto.
            eapply NoDupLocals_incl; [|econstructor; eauto]. auto. }
          assert (Is_defined_in Γ cy (Bauto Weak ck (ini0, oth) states)) as Hdef' by (eauto using Is_defined_in_Is_defined_in).
          eapply sc_var_inv_unselect with (tn:=List.length states) (sc:=stres) (Γ':=map (fun '(x, e) => (x, ann_with_clock e Cbase)) Γ); eauto.
          1:{ destruct states; try congruence. simpl; lia. }
          1:{ take (sem_transitions _ _ _ _ _ _) and eapply sem_automaton_wt_state1 in it; eauto. 1,3,4:simpl_Forall; auto.
              - inv H4. simpl_Forall; auto.
              - destruct s; destruct_conjs; intros. specialize (Hf k). destruct_conjs. simpl_Forall.
                take (sem_scope_ck' _ _ _ _ _ _) and inv it; destruct_conjs; eauto.
              - now rewrite <-H11, <-fst_InMembers. }
          1:{ intros * Hca Hck.
              eapply HasCaus_snd_det in Hca1; eauto; [|simpl_app; eauto using NoDup_app_l]; subst.
              inv Hck. inv Hca.
              split; econstructor; solve_In; auto.
          }
          1:{ intros * Hca Hck.
              eapply HasCaus_snd_det in Hca1; eauto; [|simpl_app; eauto using NoDup_app_l]; subst.
              inv Hck. inv Hca. eapply NoDupMembers_det in H; eauto. subst.
              assert (clo e = ck) as Heq; [|rewrite Heq].
              { inv Hdef. rename H1 into Hdef. simpl_Exists.
                simpl_Forall.
                destruct s. eapply wc_scope_Is_defined_in in H1; eauto.
                2:{ intros; simpl in *; simpl_Exists; simpl_Forall.
                    eapply wc_block_Is_defined_in; eauto. }
                eapply InMembers_In in H1 as (?&Hin').
                edestruct H18 as (Hck&_); eauto with senv.
                inv Hck. eapply NoDupMembers_det in H0; eauto. congruence.
              }
              rewrite <-Hac; auto.
          }
          2:{ intros * Hnin. eapply NoDup_HasCaus_HasLastCaus; eauto. solve_NoDup_app. }
          intros * Hin. rewrite <-H11 in Hin. simpl_In. simpl_Forall.
          specialize (Hf k); destruct_conjs.
          esplit; split; [|split]; eauto.
          1:{ intros ? Hca.
              eapply HasCaus_snd_det in Hca1; eauto; [|simpl_app; eauto using NoDup_app_l]; subst.
              destruct s. eapply sem_scope_defined2; eauto.
              take (sem_scope_ck' _ _ _ _ _ _) and inv it; econstructor; eauto; simpl_Forall; eauto using sem_block_ck'_sem_block.
          }
          take (forall (y : ident), _ -> _ -> _) and eapply it; eauto. inv Hca1; econstructor; solve_In. auto.
        + econstructor; eauto. simpl_Forall.
          specialize (Hf k); destruct_conjs; eauto.

      - (* automaton (strong) *)
        assert (Is_defined_in Γ cy (Bauto Strong ck ([], oth) states) \/ Is_last_in cy (Bauto Strong ck ([], oth) states) ->
                bs' ≡ abstract_clock stres) as Hac.
        { intros * Hdef.
          take (fby _ _ _) and apply ac_fby1 in it as Hac1. rewrite <-Hac1.
          symmetry. apply const_stres_ac. }
        assert (Is_defined_in Γ cy (Bauto Strong ck ([], oth) states) \/ Is_last_in cy (Bauto Strong ck ([], oth) states) ->
                bs' ≡ abstract_clock stres1) as Hac1.
        { intros * Hdef.
          take (fby _ _ _) and apply ac_fby2 in it as Hac2. rewrite Hac2; auto. }
        assert (Forall (fun '((e, _), (_, s)) => forall k, exists Hi',
                            Sem.select_hist e k stres1 Hi Hi'
                            /\ (forall y, In y xs -> HasCaus (map (fun '(x, e) => (x, ann_with_clock e Cbase)) Γ) y cy ->
                                    sc_var_inv (map (fun '(x, e) => (x, ann_with_clock e Cbase)) Γ) Hi' (fselectb e k stres1 bs) cy) /\
                              sem_scope_ck'
                                (fun Γ Hi blks => Forall (sem_block_ck' (cy::envP) Γ Hi (fselectb e k stres1 bs)) (fst blks))
                                (cy :: envP) (map (fun '(x, a) => (x, ann_with_clock a Cbase)) Γ) Hi' (fselectb e k stres1 bs) s)
                       states) as Hf.
        { simpl_Forall. intros. specialize (H25 k); destruct_conjs. destruct s; destruct_conjs.
          do 2 esplit; eauto.
          take (wt_scope _ _ _ _) and eapply sc_scope
            with (P_dep:=fun Γ cx cy blks => Exists (depends_on Γ cx cy) (fst blks))
                 (Γ:=map (fun '(x, e) => (x, ann_with_clock e Cbase)) Γ) in it as (Hsc'&?); eauto.
          - clear - H0 Hnd1.
            eapply NoDup_locals_inv3; eauto.
            unfold idcaus_of_senv in *. erewrite map_map, map_filter_map, map_ext with (l:=Γ), map_filter_ext with (xs:=Γ); eauto.
            1,2:intros; destruct_conjs; auto.
          - apply nodupmembers_map; auto.
          - erewrite map_map, map_ext; eauto. intros; destruct_conjs; auto.
          - erewrite map_map, map_ext; eauto. intros; destruct_conjs; auto.
          - apply Forall_forall; intros ? Hin. simpl_In. constructor.
          - eapply wc_scope_incl; [| |eauto|].
            + intros * Has. eapply H17 in Has as (Has&?).
              inv Has. econstructor; solve_In. auto.
            + intros * His. eapply H18 in His.
              inv His. econstructor; solve_In. auto.
            + intros; simpl in *.
              destruct_conjs; split; eauto; simpl_Forall; eauto using wc_block_incl, wc_exp_incl.
          - take (Sem.select_hist _ _ _ _ _) and destruct it as (Href&_). eapply FEnv.dom_ub_refines; eauto.
            erewrite map_map, map_ext; eauto. intros; destruct_conjs; auto.
          - intros ? His. take (Sem.select_hist _ _ _ _ _) and destruct it as (_&Heq). rewrite Heq. setoid_rewrite FEnv.map_in_iff.
            eapply Hdoml. inv His; simpl_In. econstructor; eauto.
          - intros * ? Hdep.
            assert (forall x, HasCaus Γ x cx \/ HasLastCaus Γ x cx -> In x (map fst Γ')) as Hgamma.
            { intros * Has. eapply depends_scope_In with (Γ':=Γ') (x:=x0) in Hdep; eauto with lclocking.
              - inv Hdep. rewrite <-fst_InMembers; eauto.
              - apply nodupmembers_map; auto.
              - clear - H0 Hnd1.
                eapply NoDup_locals_inv3; eauto. auto.
                unfold idcaus_of_senv in *. simpl_app.
                erewrite map_map with (l:=Γ), map_ext with (l:=Γ), map_filter_map, map_filter_ext; eauto.
                1,2:intros; destruct_conjs; auto.
              - intros ? Hin. eapply VarsDefinedScope_Is_defined with (P_def:=fun blks => Exists (Syn.Is_defined_in a) (fst blks)) in H7; eauto.
                2:eapply NoDupScope_incl; eauto. 2:intros; simpl in *; simpl_Forall; eauto using NoDupLocals_incl.
                + eapply wc_scope_Is_defined_in, fst_InMembers in H7; eauto.
                  intros; simpl_Exists; simpl_Forall; eauto using wc_block_Is_defined_in.
                + intros; inv_VarsDefined. rewrite <-Hperm in H22. apply in_concat in H22 as (?&Hin1&Hin2).
                  inv_VarsDefined; simpl_Forall. solve_Exists. eapply VarsDefined_Is_defined; eauto.
                  eapply NoDupLocals_incl; [|eauto]. rewrite <-Hperm; eauto using incl_concat.
              - destruct Has as [Has|Has]; inv Has; [left|right]; econstructor; solve_In; auto.
              - erewrite map_map, map_ext; eauto. intros; destruct_conjs; auto.
              - eapply wc_scope_wx_scope; eauto.
              - intros; simpl in *. simpl_Exists; inv_VarsDefined; simpl_Forall.
                eapply depends_on_In with (xs:=xs1); eauto using NoDup_locals_inv with lclocking.
                etransitivity; [|eauto]. rewrite <-H31; eauto using incl_concat.
            }
            assert (forall x ck', HasCaus Γ x cx \/ HasLastCaus Γ x cx -> HasClock Γ x ck' -> ck' = ck) as Hgamma2.
            { intros * Hing Hck. apply Hgamma in Hing. simpl_In.
              edestruct H17 as (Hck'&?); eauto. econstructor; solve_In; eauto.
              inv Hck. inv Hck'. eapply NoDupMembers_det in H21; eauto. congruence. }
            split; intros ??? Hca Hck Hv; inv Hca; inv Hck; simpl_In.
            1,2:eapply NoDupMembers_det in Hin0; eauto; subst.
            1,2:assert (a0.(clo) = ck) by (eapply Hgamma2; eauto with senv); subst.
            + destruct H15 as (Hfilter&_). eapply sem_var_select_inv in Hv as (?&Hv&Heq); eauto.
              apply select_fselect in Heq. rewrite Heq, ac_fselect.
              assert (depends_on Γ cy (causl a0) (Bauto Strong (clo a0) ([], oth) states)) as Hdep2.
              { eapply depends_on_incl. 3:econstructor; solve_Exists.
                1,2:intros * Has; inv Has; simpl_In; eauto with senv. }
              eapply Hsc in Hv. 4,5:eauto with senv. 2,3:eauto with senv.
              eapply sem_clock_det in Hv. 2:eapply H9.
              rewrite <-Hv, Hac1; eauto using depends_on_def_last.
              eapply sem_clock_select. rewrite <-Hac1; eauto using depends_on_def_last.
            + take (Sem.select_hist _ _ _ _ _) and destruct it as (?&Hselect). rewrite Hselect in Hv.
              eapply sem_var_fselect_inv in Hv as (?&Hv&Heq). rewrite Heq, ac_fselect.
              assert (depends_on Γ cy cx (Bauto Strong (clo a0) ([], oth) states)) as Hdep2.
              { eapply depends_on_incl. 3:econstructor; solve_Exists.
                1,2:intros * Has; inv Has; simpl_In; eauto with senv. }
              eapply Hsc in Hv. 4,5:eauto with senv. 2,3:eauto with senv.
              eapply sem_clock_det in Hv. 2:eapply H9.
              rewrite <-Hv, Hac1; eauto using depends_on_def_last.
              eapply sem_clock_select. rewrite <-Hac1; eauto using depends_on_def_last.
          - intros ? Hin' Hdep. apply HenvP. solve_In.
            eapply depends_on_incl. 3:econstructor; solve_Exists.
            1,2:intros * Has; inv Has; simpl_In; eauto with senv.
          - intros; simpl in *; simpl_Forall; inv_VarsDefined.
            eapply sem_block_ck'_refines; eauto.
            eapply NoDupLocals_incl; [|eauto]. etransitivity; eauto. rewrite <-H27; eauto using incl_concat.
          - intros; simpl in *; simpl_Forall; inv_VarsDefined.
            eapply sem_block_ck'_restrict; eauto.
            + take (wc_env _) and unfold wc_env, idck in it; simpl_Forall; auto.
            + eapply NoDupLocals_incl; [|eauto]. etransitivity; eauto. rewrite <-H29; eauto using incl_concat.
          - intros; simpl in *; destruct_conjs; split; simpl_Forall; eauto using wc_block_incl, wc_exp_incl.
          - intros; simpl in *. destruct_conjs.
            assert (Forall (fun blks => (forall y xs, VarsDefined blks xs -> In y xs -> HasCaus Γ0 y cy ->
                                              sc_var_inv Γ0 Hi0 (fselectb e k stres1 bs) cy)
                                     /\ sem_block_ck' (cy::envP) Γ0 Hi0 (fselectb e k stres1 bs) blks) l2) as Hf.
            { simpl_Forall. inv_VarsDefined.
              edestruct H with (Γ:=Γ0) (xs:=xs1). 10:eauto. all:eauto.
              - eapply NoDup_locals_inv; eauto.
              - etransitivity; eauto using incl_concat.
                take (Permutation _ _) and now rewrite it.
              - intros * Hin' Hdep. eapply H32; eauto. solve_Exists.
              - intros * Hin' Hdep. eapply H33; eauto.
                2:solve_Exists. solve_In.
              - split; eauto.
                intros * Hdef' Hin' Hca. take (forall (y: ident), _ -> _) and eapply it; eauto.
                eapply VarsDefined_det in Hdef; eauto. now rewrite <-Hdef.
            } clear H.
            split.
            + intros * Hinxs Hca. inv_VarsDefined.
              rewrite <-H36 in Hinxs. apply in_concat in Hinxs as (?&?&?); inv_VarsDefined; simpl_Forall.
              take (forall (y: ident) (xs: list ident), _ -> _) and eapply it; eauto.
            + simpl_Forall; eauto.
        } clear H H25.
        split.
        + intros * Hinxs Hca1.
          assert (Syn.Is_defined_in y (Bauto Strong ck ([], oth) states)) as Hdef.
          { eapply VarsDefined_Is_defined; eauto. econstructor; eauto.
            eapply NoDupLocals_incl; [|econstructor; eauto]. auto. }
          assert (Is_defined_in Γ cy (Bauto Strong ck ([], oth) states)) as Hdef' by (eauto using Is_defined_in_Is_defined_in).
          eapply sc_var_inv_unselect with (tn:=List.length states) (sc:=stres1) (Γ':=map (fun '(x, e) => (x, ann_with_clock e Cbase)) Γ); eauto.
          1:{ destruct states; try congruence. simpl; lia. }
          1:{ take (fby _ _ _) and eapply sem_automaton_wt_state3 in it; eauto. 2,3:simpl_Forall; auto.
              - now rewrite <-H10, <-fst_InMembers.
              - intros. specialize (H24 k); destruct_conjs. eauto. }
          1:{ intros * Hca Hck.
              eapply HasCaus_snd_det in Hca1; eauto; [|simpl_app; eauto using NoDup_app_l]; subst.
              inv Hck. inv Hca.
              split; econstructor; solve_In; auto.
          }
          1:{ intros * Hca Hck.
              eapply HasCaus_snd_det in Hca1; eauto; [|simpl_app; eauto using NoDup_app_l]; subst.
              inv Hck. inv Hca. eapply NoDupMembers_det in H; eauto. subst.
              assert (clo e = ck) as Heq; [|rewrite Heq].
              { inv Hdef. rename H1 into Hdef. simpl_Exists.
                simpl_Forall.
                destruct s. eapply wc_scope_Is_defined_in in H1; eauto.
                2:{ intros; simpl in *; simpl_Exists; simpl_Forall.
                    eapply wc_block_Is_defined_in; eauto. }
                eapply InMembers_In in H1 as (?&Hin').
                edestruct H17 as (Hck&_); eauto with senv.
                inv Hck. eapply NoDupMembers_det in H0; eauto. congruence.
              }
              rewrite <-Hac1; auto.
          }
          2:{ intros * Hnin. eapply NoDup_HasCaus_HasLastCaus; eauto. solve_NoDup_app. }
          intros * Hin. rewrite <-H10 in Hin. simpl_In. simpl_Forall.
          specialize (Hf k); destruct_conjs.
          esplit; split; [|split]; eauto.
          1:{ intros ? Hca.
              eapply HasCaus_snd_det in Hca1; eauto; [|simpl_app; eauto using NoDup_app_l]; subst.
              destruct s. eapply sem_scope_defined2; eauto.
              take (sem_scope_ck' _ _ _ _ _ _) and inv it; econstructor; eauto; simpl_Forall; eauto using sem_block_ck'_sem_block.
          }
          eapply H13; eauto. inv Hca1; econstructor; solve_In. auto.
        + econstructor; eauto. simpl_Forall.
          specialize (Hf k); destruct_conjs; eauto.

      - (* locals *)
        eapply sc_scope in H8 as (?&?); eauto with lcaus.
        + split; eauto. constructor; eauto.
        + intros. simpl_Forall. inv_VarsDefined.
          eapply sem_block_ck'_refines; eauto.
          eapply NoDupLocals_incl; [|eauto]. etransitivity; eauto. rewrite <-H11; eauto using incl_concat.
        + intros. simpl_Forall. inv_VarsDefined.
          eapply sem_block_ck'_restrict; eauto.
          * unfold wc_env, idck in H0; simpl_Forall; auto.
          * eapply NoDupLocals_incl; [|eauto]. etransitivity; eauto. rewrite <-H12; eauto using incl_concat.
        + intros; simpl in *; simpl_Forall; eauto using wc_block_incl.
        + intros.
          assert (Forall (fun blks => (forall y xs, VarsDefined blks xs -> In y xs -> HasCaus Γ0 y cy -> sc_var_inv Γ0 Hi0 bs cy)
                                     /\ sem_block_ck' (cy::envP) Γ0 Hi0 bs blks) blocks) as Hf.
            { simpl_Forall. inv_VarsDefined.
              edestruct H with (xs:=xs1). 10:eauto. all:eauto.
              - eapply NoDup_locals_inv; eauto.
              - etransitivity; eauto using incl_concat.
                take (Permutation _ _) and now rewrite it.
              - intros * Hin' Hdep. eapply H16; eauto. solve_Exists.
              - intros * Hin' Hdep. eapply H17; eauto.
                2:solve_Exists. solve_In.
              - split; eauto.
                intros * Hdef' Hin' Hca. eapply H7; eauto.
                eapply VarsDefined_det in Hdef; eauto. now rewrite <-Hdef.
            }
            split; simpl_Forall; eauto.
            intros * Hin Hca. destruct_conjs. rewrite <-H18 in Hin. apply in_concat in Hin as (?&?&?).
            inv_VarsDefined; simpl_Forall; eauto.
    Qed.

    Lemma sem_node_sc_vars :
      forall n H b,
        wc_global G ->
        wt_node G n ->
        wc_node G n ->
        node_causal n ->
        FEnv.dom H (map fst (n_in n ++ n_out n)) ->
        Forall (sc_var_inv (senv_of_inout (n_in n ++ n_out n)) (H, @FEnv.empty _) b) (map snd (idcaus (n_in n))) ->
        Sem.sem_block G (H, @FEnv.empty _) b (n_block n) ->
        sc_vars (senv_of_inout (n_in n ++ n_out n)) (H, @FEnv.empty _) b /\
        sem_block_ck' (map snd (idcaus (n_in n ++ n_out n) ++ idcaus_of_locals (n_block n)))
                      (senv_of_inout (n_in n ++ n_out n))
                      (H, @FEnv.empty _) b (n_block n).
    Proof.
      intros * HwcG Hwtn Hwcn Hcau Hdom Hins Hsem.
      assert (Forall (sc_var_inv (senv_of_inout (n_in n ++ n_out n)) (H, @FEnv.empty _) b)
                     (map snd (idcaus (n_in n ++ n_out n) ++ idcaus_of_locals (n_block n))) /\
                sem_block_ck' (map snd (idcaus (n_in n ++ n_out n) ++ idcaus_of_locals (n_block n)))
                              (senv_of_inout (n_in n ++ n_out n)) (H, @FEnv.empty _) b (n_block n)) as (?&?).
      2:{ split; auto.
          change (@nil (ident * clock)) with (idck (idty (@nil (ident * (type * clock * ident))))).
          eapply sc_var_inv_sc_vars; simpl; auto with datatypes.
          - rewrite fst_NoDupMembers, map_fst_senv_of_inout, <-fst_NoDupMembers. apply n_nodup.
          - intros * Hv. inv Hv. apply fst_InMembers in H2. rewrite map_fst_senv_of_inout in H2.
            apply Hdom in H2 as (?&?).
            do 2 esplit; eauto. reflexivity.
          - intros * Hv. inv Hv. simpl_In. congruence.
          - rewrite idcaus_of_senv_inout. eapply Forall_incl; eauto.
            solve_incl_app. }
      eapply node_causal_ind; eauto.
      - intros ?? Hperm (Hvars&Hlocs). split. rewrite <-Hperm; auto.
        eapply sem_block_ck'_Perm; eauto.
      - split; auto. apply sem_block_sem_block_ck'; auto.
      - intros ?? Hin (Hvars&Hlocs) Hdep.
        pose proof (n_defd n) as (?&Hdef&Hperm).
        pose proof (n_nodup n) as (Hnd1&Hnd2).
        destruct Hcau as (Hnd&_).
        eapply sc_block in Hlocs as (Hsc&?); eauto.
        + split; auto. constructor; auto.
          repeat rewrite idcaus_app, map_app, in_app_iff in Hin.
          rewrite or_assoc in Hin. destruct Hin as [Hin|[Hin|Hin]].
          * eapply Forall_forall in Hins; eauto.
          * simpl_In. eapply Hsc; eauto. rewrite Hperm; solve_In; eauto.
            econstructor. solve_In; eauto with datatypes. simpl; eauto. auto.
          * rewrite map_app in *.
            split; intros * Hca; exfalso; inv Hca; simpl_In.
            1,2:eapply NoDup_app_In in Hnd; eauto. 2,4:solve_In.
            1,2:eapply Hnd; simpl; solve_In. congruence.
        + rewrite idcaus_of_senv_inout; auto.
        + rewrite fst_NoDupMembers, map_fst_senv_of_inout, <-fst_NoDupMembers. apply n_nodup.
        + rewrite map_fst_senv_of_inout. apply n_nodup.
        + rewrite map_fst_senv_of_inout, Hperm. solve_incl_app.
        + eapply Hwtn.
        + unfold senv_of_inout, idck. erewrite map_map, map_ext. eapply Hwcn.
          intros; destruct_conjs; auto.
        + eapply Hwcn.
        + rewrite map_fst_senv_of_inout; eauto using FEnv.dom_dom_ub.
        + intros * Hil. inv Hil. simpl_In. congruence.
        + intros * [Hca|Hca] Hdep'; inv Hca; simpl_In; try congruence.
          eapply Forall_forall in Hvars; [|eapply Hdep]; eauto.
    Qed.

    Lemma sem_clocks_det' : forall H H' b ins vins ss,
        wc_env (map (fun '(x, (_, ck, _)) => (x, ck)) ins) ->
        Forall2 (sem_var H) (idents ins) vins ->
        Forall2 (sem_var H') (idents ins) vins ->
        Forall2 (fun xc => sem_clock H b (snd xc)) (map (fun '(x, (_, ck, _)) => (x, ck)) ins) ss ->
        Forall2 (fun xs => sem_clock H' b (snd xs)) (map (fun '(x, (_, ck, _)) => (x, ck)) ins) ss.
    Proof.
      intros * Hwc Hi1 Hi2 Hck.
      eapply sem_clocks_det in Hck; eauto.
      rewrite map_app.
      apply Forall_app; split; eapply Forall_impl; eauto; intros [? ?] ?.
      1,2:eapply wc_clock_incl; eauto.
      1,2:apply incl_appl; reflexivity.
    Qed.

    Lemma sem_node_restrict {prefs2} : forall (n : @node PSyn prefs2) H b xs ys,
        wc_block G (senv_of_inout (n_in n ++ n_out n)) (n_block n) ->
        Forall2 (sem_var H) (idents (n_in n)) xs ->
        Forall2 (sem_var H) (idents (n_out n)) ys ->
        Sem.sem_block G (H, FEnv.empty _) b (n_block n) ->
        let H' := FEnv.restrict H (idents (n_in n ++ n_out n)) in
        FEnv.dom H' (idents (n_in n ++ n_out n)) /\
        Forall2 (sem_var H') (idents (n_in n)) xs /\
        Forall2 (sem_var H') (idents (n_out n)) ys /\
        Sem.sem_block G (H', FEnv.empty _) b (n_block n).
    Proof with eauto.
      intros * Hwc Hins Houts Heqs.
      remember (FEnv.restrict _ _) as H'; simpl.
      split; [|repeat split].
      - subst. eapply FEnv.dom_lb_restrict_dom.
        intros x Hin.
        unfold idents in *.
        repeat rewrite map_app in Hin. repeat rewrite in_app_iff in Hin. destruct Hin as [Hin|Hin].
        + apply sem_vars_In in Hins. rewrite Forall_forall in Hins...
        + apply sem_vars_In in Houts. rewrite Forall_forall in Houts...
      - eapply Forall2_impl_In; [|eauto]; intros. simpl_In.
        eapply sem_var_restrict; eauto.
        eapply in_map_iff; do 2 esplit; eauto using in_or_app. reflexivity.
      - eapply Forall2_impl_In; [|eauto]; intros. simpl_In.
        eapply sem_var_restrict; eauto.
        eapply in_map_iff; do 2 esplit; eauto using in_or_app. reflexivity.
      - subst. unfold idents. eapply Sem.sem_block_restrict in Heqs; eauto with lclocking.
        rewrite map_fst_senv_of_inout in Heqs; auto.
    Qed.

    Lemma sc_var_inv_intro {prefs2} : forall (n : @node PSyn prefs2) H xs,
        node_causal n ->
        Forall2 (sem_var H) (idents (n_in n)) xs ->
        Forall2 (fun xc => sem_clock H (clocks_of xs) (snd xc)) (map (fun '(x, (_, ck, _)) => (x, ck)) (n_in n)) (map abstract_clock xs) ->
        Forall (sc_var_inv (senv_of_inout (n_in n ++ n_out n)) (H, FEnv.empty _) (clocks_of xs)) (map snd (idcaus (n_in n))).
    Proof.
      intros * (Hnd&_) Hvar Hclock.
      unfold idents, idck, idty, idcaus in *.
      simpl_Forall.
      eapply Forall2_ignore2 in Hclock. simpl_Forall.
      split; intros * Hca Hck Hv; simpl in *; inv Hca; inv Hck; simpl_In; try congruence.
      eapply NoDupMembers_det in Hin0; eauto; inv_equalities. 2:apply n_nodup.
      rewrite map_app in Hnd.
      eapply NoDup_app_l, NoDup_snd_det in Hnd. 2:solve_In.
      2:clear Hin; rewrite map_app, in_app_iff; left; solve_In. subst.
      specialize (node_NoDup n) as Hnd. apply fst_NoDupMembers in Hnd.
      eapply NoDupMembers_det in Hnd; auto.
      2:eapply in_or_app, or_introl, H0. 2:eauto. inv_equalities.
      eapply sem_var_det in H2; eauto. now rewrite H2.
    Qed.

    Fact wc_exp_Is_free_left : forall Γ e x k,
        wc_exp G Γ e ->
        Is_free_left Γ x k e ->
        In x (map snd (idcaus_of_senv Γ)).
    Proof.
      Local Ltac solve_forall_exists :=
        match goal with
        | H: Is_free_left_list _ _ _ _ |- _ =>
            eapply Is_free_left_list_Exists in H as (?&?)
        end; simpl_Exists; simpl_Forall; eauto.
      induction e using exp_ind2; intros * Hwc Hfree;
        inv Hwc; inv Hfree; eauto.
      - (* var *) solve_In. 2:eapply idcaus_of_senv_In; eauto. auto.
      - (* last *) solve_In. 2:eapply idcaus_of_senv_In; eauto. auto.
      - (* binop *) destruct H1; eauto.
      - (* fby *)
        solve_forall_exists.
      - (* arrow *)
        destruct H3 as [Hex|Hex]; eauto; solve_forall_exists.
      - (* when *)
        destruct H2 as [[? Hex]|Hex]; subst; eauto.
        + solve_In. 2:eapply idcaus_of_senv_In; eauto. auto.
        + solve_forall_exists.
      - (* merge *)
        destruct H2 as [[? Hex]|Hex]; subst; eauto.
        + solve_In. 2:eapply idcaus_of_senv_In; eauto. auto.
        + simpl_Exists. simpl_Forall.
          solve_forall_exists.
      - (* case *)
        destruct H3 as [[? Hex]|[Hex|(?&?&Hex)]]; subst; eauto.
        + simpl_Exists. simpl_Forall.
          solve_forall_exists.
        + specialize (H11 _ eq_refl). solve_forall_exists.
      - (* app *)
        destruct H13 as [(?&Hex)|Hex]; eauto.
        1,2:simpl_Exists; simpl_Forall; eauto.
    Qed.

    (** After getting sc_var_inv, we can easily give an alignment lemma for expressions *)
    Lemma sc_exp'' : forall Γ Γty H b e vs,
        wc_global G ->
        NoDupMembers Γ ->
        sc_vars Γ H b ->

        wt_exp G Γty e ->
        wc_exp G Γ e ->
        Sem.sem_exp G H b e vs ->
        Forall2 (sem_clock (fst H) b) (clockof e) (map abstract_clock vs).
    Proof.
      intros * HwcG Hnd1 Hinv Hwt Hwc Hsem.
      eapply sc_vars_sc_var_inv in Hinv; eauto.
      assert (forall k, k < numstreams e -> sc_exp_inv Γ Γty H b e k); intros.
      eapply exp_causal_ind
             with (P_exp:=sc_exp_inv _ _ H b); eauto with lclocking; intros.
      - apply sc_exp_const.
      - apply sc_exp_enum.
      - eapply sc_exp_var; eauto.
      - eapply sc_exp_last; eauto.
      - apply sc_exp_unop; auto.
      - apply sc_exp_binop; auto.
      - apply sc_exp_fby; auto.
      - apply sc_exp_arrow; auto.
      - eapply sc_exp_when; eauto.
      - eapply sc_exp_merge; eauto.
      - apply sc_exp_case; auto.
      - eapply sc_exp_app; eauto.
      - eapply Forall_forall in Hinv; eauto.
        eapply wc_exp_Is_free_left; eauto.
      - assert (length vs = numstreams e) as Hlen'.
        { eapply sem_exp_numstreams in Hsem; eauto with lclocking. }
        eapply Forall2_forall2; split.
        + rewrite map_length.
          rewrite length_clockof_numstreams; auto.
        + intros ? ? ? ? ? Hlen Hnth1 Hnth2; subst.
          rewrite length_clockof_numstreams in Hlen.
          specialize (H0 _ Hlen _ Hwt Hwc Hsem).
          rewrite nth_indep with (d':=Cbase). 2:rewrite length_clockof_numstreams; auto.
          erewrite map_nth'; eauto. setoid_rewrite Hlen'; auto.
    Qed.

    Corollary sc_exps'' : forall Γ Γty H b es vss,
        wc_global G ->
        NoDupMembers Γ ->
        sc_vars Γ H b ->

        Forall (wt_exp G Γty) es ->
        Forall (wc_exp G Γ) es ->
        Forall2 (Sem.sem_exp G H b) es vss ->
        Forall2 (sem_clock (fst H) b) (clocksof es) (map abstract_clock (concat vss)).
    Proof.
      intros * HwcG Hnd1 Hsc Hwt Hwc Hsem.
      unfold clocksof.
      rewrite Forall2_map_2, flat_map_concat_map.
      apply Forall2_concat. simpl_Forall.
      eapply sc_exp'' with (Γ:=Γ) in H1; eauto. simpl_Forall; eauto.
    Qed.

    Lemma sc_transitions'' Γty Γ : forall Hi bs' trans def stres,
        wc_global G ->
        NoDupMembers Γ ->
        Forall (fun '(e, _) => wt_exp G Γty e) trans ->
        Forall (fun '(e, _) => wc_exp G Γ e /\ clockof e = [Cbase]) trans ->
        sc_vars Γ Hi bs' ->
        sem_transitions G Hi bs' trans def stres ->
        abstract_clock stres ≡ bs'.
    Proof.
      induction trans; intros * HwG Hnd Hwt Hwc Hsc Hsem;
        inv Hwt; inv Hwc; inv Hsem; destruct_conjs.
      - rewrite H0, const_stres_ac. reflexivity.
      - rewrite H13. apply choose_first_ac; eauto.
        eapply sc_exp'' in H6; eauto.
        take (clockof _ = _) and rewrite it in H6. simpl in *. simpl_Forall.
        eapply sc_slower in H8; eauto using ac_aligned.
        apply slower_nth; intros * Hbs. setoid_rewrite Str_nth_map.
        apply slower_nth with (n:=n) in H8; auto.
        apply bools_of_nth with (n:=n) in H7 as [(Hv&Hx)|[(Hv&Hx)|(?&Hx)]].
        + setoid_rewrite H8 in Hv; congruence.
        + setoid_rewrite H8 in Hv; congruence.
        + rewrite Hx; auto.
    Qed.

  End sc_inv.

  (** Second step of the proof:
      Give clocked semantics for expressions, equations and blocks,
      given that all named streams are aligned with their clocks
   *)
  Section sem_ck.
    Context {PSyn : block -> Prop}.
    Context {prefs : PS.t}.
    Variable (G : @global PSyn prefs).

    Hypothesis HwcG : wc_global G.

    Hypothesis Hnode : forall f ins outs,
        sem_node G f ins outs ->
        sem_clock_inputs G f ins ->
        sem_node_ck G f ins outs.

    Lemma sem_exp_sem_exp_ck : forall Γ Γty H bs e vs,
        NoDupMembers Γ ->
        NoDup (map snd (idcaus_of_senv Γ)) ->
        sc_vars Γ H bs ->
        wt_exp G Γty e ->
        wc_exp G Γ e ->
        Sem.sem_exp G H bs e vs ->
        sem_exp_ck G H bs e vs.
    Proof.
      induction e using exp_ind2; intros * Hnd1 Hnd3 Hsc Hwt Hwc Hsem;
        inv Hwt; inv Hwc; inv Hsem;
          econstructor; eauto.
      1-5,10-11:(eapply Forall2_impl_In; [|eauto]; intros;
                 rewrite Forall_forall in *; eauto).
      - (* merge *)
        eapply Forall2Brs_impl_In; [|eauto]; intros ?? Hin Hse.
        simpl_Exists; simpl_Forall; eauto.
      - (* case *)
        eapply Forall2Brs_impl_In; [|eauto]; intros ?? Hin Hse.
        simpl_Exists; simpl_Forall; eauto.
      - (* case *)
        eapply Forall2Brs_impl_In; [|eauto]; intros ?? Hin Hse.
        simpl_Exists; simpl_Forall; eauto.
      - (* case (default) *)
        simpl in *.
        specialize (H23 _ eq_refl). specialize (H25 _ eq_refl).
        simpl_Forall; eauto.
      - (* app *)
        intros k. eapply Hnode; eauto.
        specialize (H26 k). inv H26. rewrite H15 in H3; inv H3.
        repeat (esplit; eauto).
        eapply sc_inside_mask with (es:=es); eauto.
        + eapply sem_exps_sem_var; eauto.
        + eapply wc_find_node in HwcG as (?&?&?); eauto.
        + eapply sc_exps'' with (Γ:=Γ); eauto.
    Qed.

    Corollary sem_equation_sem_equation_ck : forall Γ Γty H bs equ,
        NoDupMembers Γ ->
        NoDup (map snd (idcaus_of_senv Γ)) ->
        sc_vars Γ H bs ->
        wt_equation G Γty equ ->
        wc_equation G Γ equ ->
        Sem.sem_equation G H bs equ ->
        sem_equation_ck G H bs equ.
    Proof.
      intros * Hnd1 Hnd2 Hsc Hwt Hwc Hsem.
      inv Hsem. inv Hwt. inv Hwc.
      - (* app *)
        econstructor; eauto.
        apply Forall_singl in H0. inv H0.
        inv H1; inv H14. inv H5. do 2 (econstructor; eauto).
        + eapply Forall2_impl_In; [|eauto]; intros.
          eapply sem_exp_sem_exp_ck with (Γ:=Γ); eauto. 1-2:eapply Forall_forall; [|eauto]; eauto.
        + eapply Forall2_impl_In; [|eauto]; intros.
          eapply sem_exp_sem_exp_ck with (Γ:=Γ); eauto. 1-2:eapply Forall_forall; [|eauto]; eauto.
        + intros k. eapply Hnode; eauto.
          specialize (H28 k). inv H28. rewrite H1 in H17; inv H17. rewrite H1 in H8; inv H8.
          repeat (esplit; eauto).
          eapply sc_inside_mask with (es:=es0); eauto.
          * eapply sem_exps_sem_var; eauto.
          * eapply wc_find_node in HwcG as (?&?&?); eauto.
          * eapply sc_exps'' with (Γ:=Γ); eauto.
      - (* general case *)
        econstructor; eauto.
        eapply Forall2_impl_In; [|eauto]; intros.
        eapply sem_exp_sem_exp_ck with (Γ:=Γ); eauto. 1-2:eapply Forall_forall; eauto.
    Qed.

    Corollary sem_transitions_sem_transitions_ck : forall Γ Γty H bs trans def stres,
        NoDupMembers Γ ->
        NoDup (map snd (idcaus_of_senv Γ)) ->
        sc_vars Γ H bs ->
        Forall (fun '(e, _) => wt_exp G Γty e) trans ->
        Forall (fun '(e, _) => wc_exp G Γ e) trans ->
        Sem.sem_transitions G H bs trans def stres ->
        sem_transitions_ck G H bs trans def stres.
    Proof.
      induction trans; intros * Hnd1 Hnd2 Hsc Hwt Hwc Hsem; inv Hwt; inv Hwc; inv Hsem;
        econstructor; eauto using sem_exp_sem_exp_ck.
    Qed.

    Hint Resolve EqStrel EqStrel_Reflexive : core.

    Fact idcaus_of_senv_filter_NoDup : forall ck Γ,
        NoDup (map snd (idcaus_of_senv Γ)) ->
        NoDup (map snd (idcaus_of_senv (map_filter (fun '(x, e0) => if clo e0 ==b ck then Some (x, ann_with_clock e0 Cbase) else None) Γ))).
    Proof.
      intros * Hnd.
      unfold idcaus_of_senv in *. simpl_app.
      apply NoDup_app'; [apply NoDup_app_l in Hnd|apply NoDup_app_r in Hnd|].
      - induction Γ as [|(?&?)]; simpl; auto. inv Hnd.
        destruct (_ ==b _); simpl; auto. constructor; auto.
        contradict H1. solve_In.
        destruct (_ ==b _) eqn:Heq; inv Hf; rewrite equiv_decb_equiv in Heq; inv Heq; simpl in *; auto.
      - induction Γ as [|(?&?)]; simpl in *; auto.
        destruct (_ ==b _); simpl in *; (destruct (causl_last a); simpl in *; [inv Hnd|]); auto.
        constructor; auto.
        contradict H1. simpl_In.
        destruct (_ ==b _) eqn:Heq; inv Hf; rewrite equiv_decb_equiv in Heq; inv Heq; simpl in *.
        solve_In; try rewrite Hf0; simpl; eauto. auto.
      - simpl_Forall. intros contra. simpl_In.
        destruct (clo a1 ==b _) eqn:Heq; inv Hf; try rewrite equiv_decb_equiv in Heq; inv Heq; simpl in *.
        destruct (_ ==b _) eqn:Heq; inv Hf1; try rewrite equiv_decb_equiv in Heq; inv Heq; simpl in *.
        eapply NoDup_app_In; eauto. 2:solve_In; rewrite Hf0; simpl; eauto.
        clear Hin. solve_In.
    Qed.

    Lemma sem_scope_sem_scope_ck {A} f_idcaus P_nd P_vd P_wt P_wc P_blk1 (P_blk2: _ -> _ -> Prop) :
      forall envP locs caus (blk: A) xs Γty Γck Γ' H bs,
        NoDupMembers Γty ->
        NoDupMembers Γck ->
        NoDup (map snd (idcaus_of_senv Γck ++ idcaus_of_scope f_idcaus (Scope locs caus blk))) ->
        VarsDefinedScope P_vd (Scope locs caus blk) xs ->
        NoDupScope P_nd (map fst Γty) (Scope locs caus blk) ->
        incl xs (map fst Γck) ->
        (forall x ty, HasType Γck x ty -> HasType Γty x ty) ->
        incl (map snd (idcaus_of_senv Γck ++ idcaus_of_scope f_idcaus (Scope locs caus blk))) envP ->
        FEnv.dom (fst H) (map fst Γty) ->
        sc_vars Γck H bs ->
        wt_scope P_wt G Γty (Scope locs caus blk) ->
        wc_env (idck Γck) ->
        Forall (fun '(_, a) => wc_clock (idck Γck) (clo a)) Γ' ->
        wc_scope P_wc G Γck (Scope locs caus blk) ->
        sem_scope_ck' G P_blk1 envP Γ' H bs (Scope locs caus blk) ->
        (forall Γ Γ' xs Hi Hi' Hl,
            P_vd blk xs ->
            P_nd Γ blk ->
            incl xs Γ ->
            FEnv.refines (@EqSt _) Hi Hi' -> P_blk1 Γ' (Hi, Hl) blk -> P_blk1 Γ' (Hi', Hl) blk) ->
        (forall Γty Γck Γ' xs Hi Hl,
            Forall (fun '(_, a) => wc_clock (idck Γck) (clo a)) Γ' ->
            P_vd blk xs ->
            P_nd Γty blk ->
            incl xs (map fst Γck) ->
            incl (map fst Γck) Γty ->
            P_wc Γck blk ->
            P_blk1 Γ' (Hi, Hl) blk -> P_blk1 Γ' (FEnv.restrict Hi (map fst Γck), Hl) blk) ->
        (forall xs Γ Γ' Hi,
            incl xs Γ ->
            P_vd blk xs ->
            P_nd Γ blk ->
            P_blk1 Γ' Hi blk ->
            FEnv.dom_lb (fst Hi) xs) ->
        (forall xs Γty Γck Γ' Hi,
            NoDupMembers Γty ->
            NoDupMembers Γck ->
            NoDup (map snd (idcaus_of_senv Γck ++ f_idcaus blk)) ->
            P_vd blk xs ->
            P_nd (map fst Γty) blk ->
            incl xs (map fst Γck) ->
            (forall x ty, HasType Γck x ty -> HasType Γty x ty) ->
            incl (map snd (idcaus_of_senv Γck ++ f_idcaus blk)) envP ->
            FEnv.dom (fst Hi) (map fst Γty) ->
            sc_vars Γck Hi bs ->
            P_wt Γty blk ->
            wc_env (idck Γck) ->
            Forall (fun '(_, a) => wc_clock (idck Γck) (clo a)) Γ' ->
            P_wc Γck blk ->
            P_blk1 Γ' Hi blk ->
            P_blk2 Hi blk) ->
        sem_scope_ck (fun Hi => sem_exp_ck G Hi bs) P_blk2 H bs (Scope locs caus blk).
    Proof.
      intros * Hnd1 Hnd2 Hnd3 Hvd Hnd4 Hincl Hincl1 HenvP Hdom Hsc Hwt Hwenv Hwenv' Hwc Hsem Href Hres Hdom' Hind;
        inv Hvd; inv Hnd4; inv Hwt; inv Hwc; inv Hsem.
      assert (incl (map fst Γck) (map fst Γty)) as Hincl1'.
      { intros ? Hin. simpl_In. assert (HasType Γck a a0.(typ)) as Hty by eauto with senv.
        apply Hincl1 in Hty. inv Hty. solve_In. }
      assert (FEnv.dom_lb Hi' (map fst locs)) as Hdomlb.
      { eapply FEnv.dom_lb_incl. 2:eapply Hdom' in H22. 4,5:eauto. all:eauto.
        solve_incl_app. apply incl_appl'. etransitivity; eauto. }
      assert (Hi ⊑ (FEnv.restrict (Hi + Hi') (map fst Γty ++ map fst locs))) as Href1.
      { intros ?? Hfind.
        assert (In x (map fst Γty)) as Hin by (apply Hdom; econstructor; eauto).
        destruct (Hi' x) eqn:Hfind2.
        - do 2 esplit. 2:eapply FEnv.restrict_find, FEnv.union3'; eauto using in_or_app.
          eapply sem_var_det. econstructor; [eapply Hfind|reflexivity].
          eapply H6; eauto. econstructor; eauto; reflexivity.
          intro contra. eapply H8; eauto using in_or_app.
        - do 2 esplit. reflexivity.
          eapply FEnv.restrict_find, FEnv.union2; eauto using in_or_app. }
      assert (NoDupMembers (Γck ++ senv_of_locs locs)) as Hnd2'.
      { apply NoDupMembers_app; auto.
        - now apply NoDupMembers_senv_of_locs.
        - intros * Hinm1 Hinm2. rewrite InMembers_senv_of_locs in Hinm2.
          eapply H8; eauto. apply Hincl1', fst_InMembers; auto.
      }

      assert (sc_vars (Γck ++ senv_of_locs locs)
                      (FEnv.restrict (Hi + Hi') (map fst Γty ++ map fst locs), Hl') bs
             ) as Hsc'.
      { apply sc_vars_app; eauto using sc_vars_refines.
        - intros * Hinm. eapply NoDupMembers_app_InMembers in Hnd2'; eauto.
        - eapply sc_var_inv_sc_vars.
          + apply NoDupMembers_senv_of_locs; auto.
          + intros * Hv. inv Hv. rewrite fst_InMembers, map_fst_senv_of_locs in H.
            assert (Hin:=H). apply Hdomlb in H as (?&Hfind).
            do 2 eexists; try reflexivity.
            eapply FEnv.restrict_find, FEnv.union3'; eauto.
            apply in_or_app, or_intror; solve_In.
          + intros * Hv. inv Hv. simpl_In. destruct o as [(?&?)|]; simpl in *; try congruence.
            edestruct H18 as (?&?&?&?&?&?&?); eauto.
          + simpl_Forall.
            assert (In i0 envP) as HinP.
            { eapply HenvP.
              rewrite 2 map_app, 2 in_app_iff. right; left. solve_In. }
            simpl_Forall.
            take (sc_var_inv _ _ _ _) and destruct it as (Hsc1'&Hsc2').
            split; intros * Hca Hck Hv.
            1,2:eapply sem_clock_refines'. 3:eapply Hsc1'; eauto.
            6:eapply Hsc2'; eauto.
            * inv Hck. simpl_In. eapply Forall_forall in H15; [|solve_In; eauto]; simpl in *.
              eapply wc_clock_wx_clock in H15; eauto.
            * intros * Hin Hv'. inv Hin. rewrite fst_InMembers, map_app, map_fst_senv_of_locs in H0.
              eapply sem_var_restrict; eauto.
              rewrite in_app_iff in *. destruct H0; eauto.
            * eapply sem_var_restrict_inv in Hv as (?&?); eauto.
            * inv Hck. simpl_In. eapply Forall_forall in H15; [|solve_In; eauto]; simpl in *.
              eapply wc_clock_wx_clock in H15; eauto.
            * intros * Hin Hv'. inv Hin. rewrite fst_InMembers, map_app, map_fst_senv_of_locs in H0.
              eapply sem_var_restrict; eauto.
              rewrite in_app_iff in *. destruct H0; eauto.
      }
      assert (FEnv.dom (FEnv.restrict (Hi + Hi') (map fst Γty ++ map fst locs)) (map fst Γty ++ map fst locs)) as Hdom''.
      { eapply FEnv.dom_lb_restrict_dom, FEnv.dom_lb_incl, FEnv.union_dom_lb; eauto using FEnv.dom_dom_lb.
        now rewrite Permutation_app_comm. }

      eapply Sscope with (Hi':=FEnv.restrict (Hi + Hi') (map fst Γty ++ map fst locs)); eauto.
      - intros * Hvar Hnin1.
        apply sem_var_restrict_inv in Hvar as (Hin&Hvar). apply sem_var_union in Hvar as [|Hvar]; auto.
      - intros. specialize (Hdom x). specialize (Hdom'' x).
        now rewrite Hdom, Hdom'', in_app_iff, <-2 fst_InMembers.
      - intros. edestruct H18; destruct_conjs; eauto.
        do 3 esplit. repeat split; eauto using sem_var_refines.
        + simpl_Forall.
          rewrite <-map_fst_senv_of_locs, <-map_app.
          eapply sem_exp_sem_exp_ck with (Γ:=Γck ++ _), Sem.sem_exp_restrict, Sem.sem_exp_refines; eauto using FEnv.union_refines4'.
          * clear - Hnd3. rewrite idcaus_of_senv_app. solve_NoDup_app.
          * rewrite map_app, map_fst_senv_of_locs; auto.
          * eauto with ltyping.
        + eapply sem_var_restrict, sem_var_refines; eauto using FEnv.union_refines4'.
          apply in_app_iff, or_intror. solve_In.
      - clear - Hsc'. destruct Hsc' as (Hsc1&Hsc2).
        setoid_rewrite IsLast_app in Hsc2.
        setoid_rewrite HasClock_app in Hsc1. setoid_rewrite HasClock_app in Hsc2.
        split; eauto.
      - eapply Hind with (Γ':=replace_idcaus caus Γ'++senv_of_locs locs) (Γty:=Γty++_); eauto.
        + apply NoDupMembers_app; auto.
          * apply NoDupMembers_senv_of_locs; auto.
          * intros * Hinm1 Hinm2. rewrite InMembers_senv_of_locs in Hinm2.
            eapply H8; eauto. apply fst_InMembers; auto.
        + clear - Hnd3. simpl in *.
          rewrite idcaus_of_senv_app.
          simpl_app. auto.
          solve_NoDup_app.
        + rewrite map_app, map_fst_senv_of_locs; auto.
        + rewrite map_app, map_fst_senv_of_locs. now apply incl_appl'.
        + intros *. rewrite 2 HasType_app. intros [|]; auto.
        + etransitivity; [|eauto].
          rewrite idcaus_of_senv_app. simpl_app. solve_incl_app.
        + now rewrite map_app, map_fst_senv_of_locs.
        + simpl_app. eapply Forall_app; split; eauto.
          * eapply Forall_impl; [|eauto]; intros; simpl in *.
            eapply wc_clock_incl; [|eauto]. solve_incl_app.
          * simpl_Forall; eauto.
        + apply Forall_app; split; simpl_Forall; simpl_In; simpl_Forall; eauto.
          destruct (assoc_ident _ _); (eapply wc_clock_incl; [|eauto]); solve_incl_app.
        + rewrite <-map_fst_senv_of_locs, <-map_app.
          eapply Href. 1,2:eauto. apply incl_appl'; etransitivity; eauto.
          eapply FEnv.incl_restrict_refines; eauto using EqStrel_Transitive.
          2:eapply Hres, Href.
          2:{ apply Forall_app; split; simpl_Forall; simpl_In; simpl_Forall; eauto.
              destruct (assoc_ident _ _); (eapply wc_clock_incl; [|eauto]); solve_incl_app. }
          2-3,6-8,10-11:eauto using FEnv.union_refines4'.
          all:repeat rewrite map_app; repeat rewrite map_fst_senv_of_locs; apply incl_appl'; auto.
          etransitivity; eauto.
    Qed.

    Local Ltac simpl_ndup Hnd :=
      simpl in *;
      try rewrite app_nil_r in Hnd; repeat rewrite map_app.

    Lemma sem_block_sem_block_ck : forall envP blk xs Γty Γck Γ' H bs,
        NoDupMembers Γty ->
        NoDupMembers Γck ->
        NoDup (map snd (idcaus_of_senv Γck ++ idcaus_of_locals blk)) ->
        VarsDefined blk xs ->
        NoDupLocals (map fst Γty) blk ->
        incl xs (map fst Γck) ->
        (forall x ty, HasType Γck x ty -> HasType Γty x ty) ->
        incl (map snd (idcaus_of_senv Γck ++ idcaus_of_locals blk)) envP ->
        FEnv.dom (fst H) (map fst Γty) ->
        sc_vars Γck H bs ->
        wt_block G Γty blk ->
        wc_env (idck Γck) ->
        Forall (fun '(_, a) => wc_clock (idck Γck) (clo a)) Γ' ->
        wc_block G Γck blk ->
        sem_block_ck' G envP Γ' H bs blk ->
        sem_block_ck G H bs blk.
    Proof.
      induction blk using block_ind2;
        intros * Hnd1 Hnd2 Hnd5 Hvars Hnd6 Hincl Hincl1 HenvP Hdom Hsc Hwt Hwenv Hwenv' Hwc Hsem;
        inv Hnd6; inv Hvars; inv Hwt; inv Hwc; inv Hsem; simpl_ndup Hnd1.

      - (* equation *)
        constructor. eapply sem_equation_sem_equation_ck with (Γ:=Γck); eauto.
        rewrite app_nil_r in Hnd5; auto.

      - (* reset *)
        econstructor; eauto.
        + assert (Hsem2:=H7).
          eapply sem_exp_sem_exp_ck with (Γ:=Γck) in Hsem2; eauto.
          rewrite map_app in Hnd5; eauto using NoDup_app_l.
        + intros k. specialize (H16 k). simpl_Forall. inv_VarsDefined.
          eapply H with (Γty:=Γty); eauto.
          * eapply NoDup_locals_inv; eauto.
          * etransitivity; eauto using incl_concat.
          * etransitivity; [|eauto]. rewrite 2 map_app. apply incl_appr'.
            intros ??. solve_In.
          * eapply FEnv.dom_map; eauto.
          * eapply sc_vars_mask; eauto.

      - (* switch *)
        assert (sem_clock (fst H0) bs ck (abstract_clock sc)) as Hsemck.
        { eapply sc_exp'' with (Γ:=Γck) in H16; eauto.
          take (clockof _ = _) and rewrite it in H16; simpl_Forall; eauto.
        }
        assert (incl (map fst Γck) (map fst Γty)) as Hincl'.
        { intros ? Hv. simpl_In. assert (HasType Γck a a0.(typ)) as Hty by eauto with senv.
          specialize (Hincl1 _ _ Hty). inv Hincl1. do 2 esplit; eauto. auto. }

        econstructor; eauto.
        + eapply sem_exp_sem_exp_ck with (Γ:=Γck) in H16; eauto.
          solve_NoDup_app.
        + simpl_Forall.
          destruct H0 as (Hfilter1&Hfilter2).
          apply filter_hist_ffilter_hist in Hfilter1.
          do 2 esplit; eauto.
          1:{ instantiate (1:=(_, _)). split; simpl; eauto.
              take (wt_streams _ _) and rewrite H7 in it. apply Forall2_singl in it.
              eapply filter_hist_restrict_ac with (xs:=map fst Γ'0); eauto.
              intros * Hin Hvar. simpl_In.
              destruct Hsc as ((?&Hv&Hck)&_). eapply H15; eauto with senv.
              eapply sem_var_det in Hvar; eauto. rewrite <-Hvar.
              eapply sem_clock_det in Hsemck; eauto.
          }
          destruct s. eapply sem_scope_restrict; eauto.
          1:{ apply Forall_forall. intros * Hin; simpl_In.
              edestruct H15 as (?&Hbase); eauto with senv. rewrite Hbase. constructor. }
          2:{ intros; simpl_Forall. eapply sem_block_restrict; eauto. }
          eapply sem_scope_sem_scope_ck
            with (Γty:=Γty)
                 (Γck:=map_filter (fun '(x, e) => if e.(clo) ==b ck then Some (x, ann_with_clock e Cbase) else None) Γck)
                 (Γ':=map (fun '(x, a) => (x, ann_with_clock a Cbase)) Γ'); eauto.
          * eapply nodupmembers_map_filter; eauto.
            intros *. destruct (_ ==b _); simpl; auto.
          * subst. eapply NoDup_locals_inv2; eauto.
            rewrite map_app in *. eapply NoDup_incl_app2. 3:apply Hnd5.
            -- intros ? Hin. unfold idcaus_of_senv in *. rewrite map_app, in_app_iff in *.
               destruct Hin; [left|right]; simpl_In; destruct (_ ==b _) eqn:Heq; inv Hf; rewrite equiv_decb_equiv in Heq; inv Heq; simpl in *.
               1,2:solve_In; try rewrite Hf0; simpl; eauto. auto.
            -- intros Hnd. eapply idcaus_of_senv_filter_NoDup; eauto.
          * intros ? Hin.
            eapply VarsDefinedScope_Is_defined with (P_def:=Exists (Syn.Is_defined_in a)) in H6; eauto.
            2:{ eapply NoDupScope_incl ; [| |eauto]. 2:etransitivity; eauto using incl_concat.
                intros; simpl in *; simpl_Forall. eauto using NoDupLocals_incl. }
            2:{ intros; simpl in *. inv_VarsDefined. eapply Forall_VarsDefined_Is_defined; eauto.
                simpl_Forall. 1,2:now rewrite Hperm. }
            eapply wc_scope_Is_defined_in, InMembers_In in H6 as (?&?); eauto.
            2:{ intros; simpl in *. eapply Exists_Is_defined_in_wx_In; [|eauto].
                simpl_Forall; eauto with lclocking. }
            edestruct H15; eauto with senv. inv H6. solve_In.
            2:rewrite equiv_decb_refl; eauto. auto.
          * subst. intros * Hty. apply Hincl1.
            inv Hty. simpl_In.
            destruct (_ ==b _) eqn:Heq; inv Hf; rewrite equiv_decb_equiv in Heq. eauto with senv.
          * subst. etransitivity; [|eapply HenvP].
            rewrite 2 map_app. apply incl_app; [apply incl_appl|apply incl_appr; intros ??; solve_In].
            unfold idcaus_of_senv. simpl_app. repeat rewrite map_map.
            apply incl_app; [apply incl_appl|apply incl_appr].
            1-2:intros ??; solve_In. 1,3:destruct (_ ==b _); inv Hf; eauto; simpl in *. rewrite Hf0; simpl; eauto. auto.
          * apply FEnv.dom_map. auto.
          * eapply sc_vars_morph, sc_vars_ffilter with (Γ:=Γck); eauto. 2:reflexivity.
            -- split; try reflexivity. rewrite <-Hfilter2; reflexivity.
            -- subst. intros * Hck. inv Hck; simpl_In.
               destruct (_ ==b _) eqn:Heq; inv Hf; rewrite equiv_decb_equiv in Heq; inv Heq.
               eauto with senv.
            -- subst. intros * Hca. inv Hca; simpl_In.
               destruct (_ ==b _) eqn:Heq; inv Hf; rewrite equiv_decb_equiv in Heq; inv Heq.
               eauto with senv.
          * subst. eapply Forall_forall; intros ? Hin. simpl_In.
            destruct (_ ==b _) eqn:Heq; inv Hf; rewrite equiv_decb_equiv in Heq; inv Heq.
            constructor.
          * simpl_Forall. constructor.
          * eapply wc_scope_incl; [| |eauto|].
            1,2:intros * Hin.
            -- eapply H15 in Hin as (Hck&?); subst.
               inv Hck. econstructor; solve_In; auto. simpl. rewrite equiv_decb_refl; eauto. auto.
            -- assert (exists ck, HasClock Γ'0 x ck) as (?&Hck) by (inv Hin; eauto with senv).
               eapply H15 in Hck as (Hck&?); subst.
               eapply H17 in Hin as Hil; subst.
               inv Hil. inv Hck. eapply NoDupMembers_det in H0; eauto; subst.
               econstructor; solve_In; auto. simpl. rewrite equiv_decb_refl; eauto. auto.
            -- intros; simpl in *; simpl_Forall; eauto using wc_block_incl.
          * eapply sem_scope_ck'_refines1. 2-5:eauto.
            etransitivity; eauto.
          * intros; simpl in *; simpl_Forall; inv_VarsDefined. eapply sem_block_ck'_refines; eauto.
            eapply NoDupLocals_incl; [|eauto]. etransitivity; eauto. rewrite <-H25; eauto using incl_concat.
          * intros; simpl in *; simpl_Forall; inv_VarsDefined. eapply sem_block_ck'_restrict; eauto.
            eapply NoDupLocals_incl; [|eauto]. do 2 (etransitivity; eauto). rewrite <-H27; eauto using incl_concat.
          * intros; simpl in *; simpl_Forall; inv_VarsDefined.
            destruct Hi. eapply Forall_sem_block_dom_lb; eauto; simpl_Forall; eauto using NoDupLocals_incl, sem_block_ck'_sem_block.
          * intros; simpl in *; simpl_Forall. inv_VarsDefined.
            eapply H with (Γty:=Γty0); eauto using NoDup_locals_inv.
            -- etransitivity; eauto. rewrite <-H35; eauto using incl_concat.
            -- etransitivity; eauto. rewrite 2 map_app. apply incl_appr'. intros ??; solve_In.

      - (* automaton (weak) *)
        assert (sc_vars (map_filter (fun '(x, e) => if clo e ==b ck then Some (x, ann_with_clock e Cbase) else None) Γck) H0 bs') as Hsc'.
        { eapply sc_vars_subclock. 1,4:eauto.
          - intros * Hck; inv Hck; simpl_In.
            destruct (_ ==b _) eqn:Heq; inv Hf. rewrite equiv_decb_equiv in Heq; inv Heq.
            eauto with senv.
          - intros * Hl; inv Hl; simpl_In.
            destruct (_ ==b _) eqn:Heq; inv Hf. rewrite equiv_decb_equiv in Heq; inv Heq.
            eauto with senv.
        }
        assert (bs' ≡ abstract_clock stres) as Hac.
        { symmetry. take (sem_transitions _ _ _ _ _ _) and eapply sc_transitions''
            with (Γ:=map_filter (fun '(x, e) => if e.(clo) ==b ck then Some (x, ann_with_clock e Cbase) else None) Γck) in it; eauto. 3,4:simpl_Forall; eauto.
          - take (fby _ _ _) and apply ac_fby1 in it; now rewrite <-it.
          - apply nodupmembers_map_filter; auto.
            intros; destruct (_ ==b _); simpl; auto.
          - split; auto.
            eapply wc_exp_incl; [| |eauto].
            + intros * Has. eapply H19 in Has as (Has&?).
              inv Has. econstructor. solve_In; simpl. rewrite equiv_decb_refl; eauto.
              auto.
            + intros * His. eapply H20 in His as His'.
              inv His; inv His'. edestruct H19 as (Has&?); eauto with senv.
              inv Has. eapply NoDupMembers_det in H21; eauto; subst.
              econstructor. solve_In; simpl. rewrite equiv_decb_refl; eauto.
              simpl; auto.
        }
        assert (incl (map fst Γck) (map fst Γty)) as Hincl'.
        { intros ? Hv. simpl_In. assert (HasType Γck a a0.(typ)) as Hty by eauto with senv.
          specialize (Hincl1 _ _ Hty). inv Hincl1. do 2 esplit; eauto. auto. }

        econstructor; eauto.
        + eapply sem_transitions_sem_transitions_ck with (Γ:=map_filter (fun '(x, e) => if e.(clo) ==b ck then Some (x, ann_with_clock e Cbase) else None) Γck); eauto. 3,4:simpl_Forall; eauto.
          * apply nodupmembers_map_filter; auto.
            intros; destruct (_ ==b _); simpl; auto.
          * rewrite map_app in Hnd5. apply idcaus_of_senv_filter_NoDup; eauto using NoDup_app_l.
          * eapply wc_exp_incl; [| |eauto].
            -- intros * Has. eapply H19 in Has as (Has&?).
               inv Has. econstructor. solve_In; simpl. rewrite equiv_decb_refl; eauto.
               auto.
            -- intros * His. eapply H20 in His as His'.
               inv His; inv His'. edestruct H19 as (Has&?); eauto with senv.
               inv Has. eapply NoDupMembers_det in H21; eauto; subst.
               econstructor. solve_In; simpl. rewrite equiv_decb_refl; eauto.
               simpl; auto.
        + simpl_Forall. take (forall k, _) and specialize (it k); destruct_conjs.
          take (Sem.select_hist _ _ _ _ _) and destruct it as (Hsel1&Hsel2).
          apply select_hist_fselect_hist in Hsel1.
          eapply sc_vars_fselect with (Γ':=map_filter (fun '(x, e) => if e.(clo) ==b ck then Some (x, ann_with_clock e Cbase) else None) Γck) in Hsc as Hsc''.
          2:rewrite <-Hac; eauto.
          2:{ intros * Has. inv Has; simpl_In. destruct (_ ==b _) eqn:Heq; inv Hf; rewrite equiv_decb_equiv in Heq; inv Heq.
              eauto with senv. }
          2:{ intros * Has. inv Has; simpl_In. destruct (_ ==b _) eqn:Heq; inv Hf; rewrite equiv_decb_equiv in Heq; inv Heq.
              eauto with senv. }
          esplit; split.
          1:{ instantiate (1:=(_, _)). split; simpl; eauto.
              eapply select_hist_restrict_ac with (xs:=map fst Γ'0); eauto.
              intros * Hin Hvar. simpl_In.
              destruct Hsc as ((?&Hv&Hck)&_). eapply H19; eauto with senv.
              eapply sem_var_det in Hvar; eauto. rewrite <-Hvar.
              rewrite <-Hac. eapply sem_clock_det; eauto.
          }
          destruct s; destruct_conjs. eapply sem_scope_restrict; eauto.
          1:{ apply Forall_forall. intros * Hin; simpl_In.
              edestruct H19 as (?&Hbase); eauto with senv. rewrite Hbase. constructor. }
          2:{ intros; destruct_conjs; split; simpl_Forall; eauto using sem_block_restrict.
              eapply sem_transitions_restrict; eauto. simpl_Forall; eauto with lclocking. }
          eapply sem_scope_sem_scope_ck
            with (Γty:=Γty)
                 (Γck:=map_filter (fun '(x, e) => if e.(clo) ==b ck then Some (x, ann_with_clock e Cbase) else None) Γck)
                 (Γ':=map (fun '(x, a) => (x, ann_with_clock a Cbase)) Γ'); eauto.
          * subst. eapply nodupmembers_map_filter; eauto.
            intros *. destruct (_ ==b _); simpl; auto.
          * subst. eapply NoDup_locals_inv3; eauto.
            rewrite map_app in *. eapply NoDup_incl_app2. 3:apply Hnd5.
            -- intros ? Hin. unfold idcaus_of_senv in *. rewrite map_app, in_app_iff in *.
               destruct Hin; [left|right]; simpl_In; destruct (_ ==b _) eqn:Heq; inv Hf; rewrite equiv_decb_equiv in Heq; inv Heq; simpl in *.
               1,2:solve_In; try rewrite Hf0; simpl; eauto. auto.
            -- intros Hnd. eapply idcaus_of_senv_filter_NoDup; eauto.
          * intros ? Hin.
            eapply VarsDefinedScope_Is_defined with (P_def:=fun blks => Exists (Syn.Is_defined_in a) (fst blks)) in H8; eauto.
            2:{ eapply NoDupScope_incl ; [| |eauto]. 2:etransitivity; eauto using incl_concat.
                intros; simpl in *; simpl_Forall. eauto using NoDupLocals_incl. }
            2:{ intros; simpl in *. inv_VarsDefined. eapply Forall_VarsDefined_Is_defined; eauto.
                simpl_Forall. 1,2:now rewrite Hperm. }
            eapply wc_scope_Is_defined_in, InMembers_In in H8 as (?&?); eauto.
            2:{ intros; simpl in *. eapply Exists_Is_defined_in_wx_In; [|eauto].
                simpl_Forall; eauto with lclocking. }
            edestruct H19; eauto with senv. take (HasClock _ _ _) and inv it. solve_In.
            2:rewrite equiv_decb_refl; eauto. auto.
          * subst. intros * Hty. apply Hincl1.
            inv Hty. simpl_In.
            destruct (_ ==b _) eqn:Heq; inv Hf; rewrite equiv_decb_equiv in Heq. eauto with senv.
          * subst. etransitivity; [|eapply HenvP].
            rewrite 2 map_app. apply incl_app; [apply incl_appl|apply incl_appr; intros ??; solve_In].
            unfold idcaus_of_senv. simpl_app. repeat rewrite map_map.
            apply incl_app; [apply incl_appl|apply incl_appr].
            1-2:intros ??; solve_In. 1,3:destruct (_ ==b _); inv Hf; eauto; simpl in *. rewrite Hf0; simpl; eauto. auto.
          * apply FEnv.dom_map. auto.
          * eapply sc_vars_morph; eauto. 2:reflexivity.
            split; try reflexivity. rewrite Hsel2; reflexivity.
          * subst. eapply Forall_forall; intros ? Hin. simpl_In.
            destruct (_ ==b _) eqn:Heq; inv Hf; rewrite equiv_decb_equiv in Heq; inv Heq.
            constructor.
          * simpl_Forall. constructor.
          * eapply wc_scope_incl; [| |eauto|].
            1,2:intros * Hin.
            -- eapply H19 in Hin as (Hck&?); subst.
               inv Hck. econstructor; solve_In; auto. simpl. rewrite equiv_decb_refl; eauto. auto.
            -- assert (exists ck, HasClock Γ'0 x ck) as (?&Hck) by (inv Hin; eauto with senv).
               eapply H19 in Hck as (Hck&?); subst.
               eapply H20 in Hin as Hil; subst.
               inv Hil. inv Hck. eapply NoDupMembers_det in H4; eauto; subst.
               econstructor; solve_In; auto. simpl. rewrite equiv_decb_refl; eauto. auto.
            -- intros; simpl in *; destruct_conjs; split; simpl_Forall; eauto using wc_block_incl.
               split; eauto using wc_exp_incl.
          * eapply sem_scope_ck'_refines2. 2-5:eauto.
            etransitivity; eauto.
          * intros; simpl in *; destruct_conjs; split; simpl_Forall; inv_VarsDefined; eauto using Sem.sem_transitions_refines.
            eapply sem_block_ck'_refines; eauto.
            eapply NoDupLocals_incl; [|eauto]. etransitivity; eauto. take (Permutation _ _) and rewrite <-it; eauto using incl_concat.
          * intros; simpl in *; destruct_conjs; split; simpl_Forall; inv_VarsDefined.
            -- eapply sem_block_ck'_restrict; eauto.
               eapply NoDupLocals_incl; [|eauto]. do 2 (etransitivity; eauto). take (Permutation _ _) and rewrite <-it; eauto using incl_concat.
            -- eapply Sem.sem_transitions_restrict; eauto. simpl_Forall; eauto with lclocking.
          * intros; simpl in *; simpl_Forall; inv_VarsDefined.
            destruct Hi. eapply Forall_sem_block_dom_lb; eauto; simpl_Forall; eauto using NoDupLocals_incl, sem_block_ck'_sem_block.
          * intros; simpl in *; destruct_conjs; split.
            2:{ eapply sem_transitions_sem_transitions_ck; eauto.
                2,3:simpl_Forall; eauto. solve_NoDup_app. }
            simpl_Forall. inv_VarsDefined.
            eapply H with (Γty:=Γty0); eauto using NoDup_locals_inv.
            -- etransitivity; eauto. take (Permutation _ _) and rewrite <-it; eauto using incl_concat.
            -- etransitivity; eauto. rewrite 2 map_app. apply incl_appr'. intros ??; solve_In.

      - (* automaton (strong) *)
        assert (sc_vars (map_filter (fun '(x, e) => if clo e ==b ck then Some (x, ann_with_clock e Cbase) else None) Γck) H0 bs') as Hsc'.
        { eapply sc_vars_subclock. 1,4:eauto.
          - intros * Hck; inv Hck; simpl_In.
            destruct (_ ==b _) eqn:Heq; inv Hf. rewrite equiv_decb_equiv in Heq; inv Heq.
            eauto with senv.
          - intros * Hl; inv Hl; simpl_In.
            destruct (_ ==b _) eqn:Heq; inv Hf. rewrite equiv_decb_equiv in Heq; inv Heq.
            eauto with senv.
        }
        assert (bs' ≡ abstract_clock stres) as Hac.
        { symmetry. take (fby _ _ _) and apply ac_fby1 in it; rewrite <-it. apply const_stres_ac. }
        assert (bs' ≡ abstract_clock stres1) as Hac1.
        { take (fby _ _ _) and apply ac_fby2 in it; now rewrite it. }

        assert (incl (map fst Γck) (map fst Γty)) as Hincl'.
        { intros ? Hv. simpl_In. assert (HasType Γck a a0.(typ)) as Hty by eauto with senv.
          specialize (Hincl1 _ _ Hty). inv Hincl1. do 2 esplit; eauto. auto. }

        econstructor; eauto.
        + simpl_Forall. specialize (H25 k); destruct_conjs.
          take (Sem.select_hist _ _ _ _ _) and destruct it as (Hsel1&Hsel2).
          apply select_hist_fselect_hist in Hsel1.
          eapply sc_vars_fselect with (Γ':=map_filter (fun '(x, e) => if e.(clo) ==b ck then Some (x, ann_with_clock e Cbase) else None) Γck) in Hsc as Hsc''.
          2:rewrite <-Hac; eauto.
          2:{ intros * Has. inv Has; simpl_In. destruct (_ ==b _) eqn:Heq; inv Hf; rewrite equiv_decb_equiv in Heq; inv Heq.
              eauto with senv. }
          2:{ intros * Has. inv Has; simpl_In. destruct (_ ==b _) eqn:Heq; inv Hf; rewrite equiv_decb_equiv in Heq; inv Heq.
              eauto with senv. }
          do 2 esplit.
          1:{ instantiate (1:=(_,_)). split; simpl; eauto.
              eapply select_hist_restrict_ac with (xs:=map fst Γ'0); eauto.
              intros * Hin Hvar. simpl_In.
              destruct Hsc as ((?&Hv&Hck)&_). eapply H18; eauto with senv.
              eapply sem_var_det in Hvar; eauto. rewrite <-Hvar.
              rewrite <-Hac. eapply sem_clock_det; eauto.
          }
          eapply sem_transitions_restrict, sem_transitions_sem_transitions_ck
            with (Γ:=map_filter (fun '(x, e) => if e.(clo) ==b ck then Some (x, ann_with_clock e Cbase) else None) Γck); eauto.
          1,5,6:simpl_Forall; eauto with lclocking.
          * eapply wc_exp_incl; [| |eauto].
            -- intros * Has. eapply H18 in Has as (Has&?).
               inv Has. econstructor. solve_In; simpl. rewrite equiv_decb_refl; eauto.
               auto.
            -- intros * His. eapply H19 in His as His'.
               inv His; inv His'. edestruct H18 as (Has&?); eauto with senv.
               inv Has. eapply NoDupMembers_det in H27; eauto; subst.
               econstructor. solve_In; simpl. rewrite equiv_decb_refl; eauto.
               simpl; auto.
          * apply nodupmembers_map_filter; auto.
            intros; destruct (_ ==b _); simpl; auto.
          * rewrite map_app in Hnd5. apply idcaus_of_senv_filter_NoDup; eauto using NoDup_app_l.
          * eapply sc_vars_morph; [reflexivity| |reflexivity|eauto].
            split; try reflexivity. symmetry; auto.
          * simpl; eapply Sem.sem_transitions_refines; eauto.
        + simpl_Forall. specialize (H26 k); destruct_conjs.
          take (Sem.select_hist _ _ _ _ _) and destruct it as (Hsel1&Hsel2).
          apply select_hist_fselect_hist in Hsel1.
          eapply sc_vars_fselect with (Γ':=map_filter (fun '(x, e) => if e.(clo) ==b ck then Some (x, ann_with_clock e Cbase) else None) Γck) in Hsc as Hsc''.
          2:rewrite <-Hac1; eauto.
          2:{ intros * Has. inv Has; simpl_In. destruct (_ ==b _) eqn:Heq; inv Hf; rewrite equiv_decb_equiv in Heq; inv Heq.
              eauto with senv. }
          2:{ intros * Has. inv Has; simpl_In. destruct (_ ==b _) eqn:Heq; inv Hf; rewrite equiv_decb_equiv in Heq; inv Heq.
              eauto with senv. }
          esplit; split.
          1:{ instantiate (1:=(_, _)). split; simpl; eauto.
              eapply select_hist_restrict_ac with (xs:=map fst Γ'0); eauto.
              intros * Hin Hvar. simpl_In.
              destruct Hsc as ((?&Hv&Hck)&_). eapply H18; eauto with senv.
              eapply sem_var_det in Hvar; eauto. rewrite <-Hvar.
              rewrite <-Hac1. eapply sem_clock_det; eauto.
          }
          destruct s; destruct_conjs. eapply sem_scope_restrict; eauto.
          1:{ apply Forall_forall. intros * Hin; simpl_In.
              edestruct H18 as (?&Hbase); eauto with senv. rewrite Hbase. constructor. }
          2:{ intros; simpl_Forall; eauto using sem_block_restrict. }
          eapply sem_scope_sem_scope_ck
            with (Γty:=Γty)
                 (Γck:=map_filter (fun '(x, e) => if e.(clo) ==b ck then Some (x, ann_with_clock e Cbase) else None) Γck)
                 (Γ':=map (fun '(x, a) => (x, ann_with_clock a Cbase)) Γ'); eauto.
          * subst. eapply nodupmembers_map_filter; eauto.
            intros *. destruct (_ ==b _); simpl; auto.
          * subst. eapply NoDup_locals_inv3; eauto.
            rewrite map_app in *. eapply NoDup_incl_app2. 3:apply Hnd5.
            -- intros ? Hin. unfold idcaus_of_senv in *. rewrite map_app, in_app_iff in *.
               destruct Hin; [left|right]; simpl_In; destruct (_ ==b _) eqn:Heq; inv Hf; rewrite equiv_decb_equiv in Heq; inv Heq; simpl in *.
               1,2:solve_In; try rewrite Hf0; simpl; eauto. auto.
            -- intros Hnd. eapply idcaus_of_senv_filter_NoDup; eauto.
          * intros ? Hin.
            eapply VarsDefinedScope_Is_defined with (P_def:=fun blks => Exists (Syn.Is_defined_in a) (fst blks)) in H8; eauto.
            2:{ eapply NoDupScope_incl ; [| |eauto]. 2:etransitivity; eauto using incl_concat.
                intros; simpl in *; simpl_Forall. eauto using NoDupLocals_incl. }
            2:{ intros; simpl in *. inv_VarsDefined. eapply Forall_VarsDefined_Is_defined; eauto.
                simpl_Forall. 1,2:now rewrite Hperm. }
            eapply wc_scope_Is_defined_in, InMembers_In in H8 as (?&?); eauto.
            2:{ intros; simpl in *. eapply Exists_Is_defined_in_wx_In; [|eauto].
                simpl_Forall; eauto with lclocking. }
            edestruct H18; eauto with senv. take (HasClock _ _ _) and inv it. solve_In.
            2:rewrite equiv_decb_refl; eauto. auto.
          * subst. intros * Hty. apply Hincl1.
            inv Hty. simpl_In.
            destruct (_ ==b _) eqn:Heq; inv Hf; rewrite equiv_decb_equiv in Heq. eauto with senv.
          * subst. etransitivity; [|eapply HenvP].
            rewrite 2 map_app. apply incl_app; [apply incl_appl|apply incl_appr; intros ??; solve_In].
            unfold idcaus_of_senv. simpl_app. repeat rewrite map_map.
            apply incl_app; [apply incl_appl|apply incl_appr].
            1-2:intros ??; solve_In. 1,3:destruct (_ ==b _); inv Hf; eauto; simpl in *. rewrite Hf0; simpl; eauto. auto.
          * apply FEnv.dom_map. auto.
          * eapply sc_vars_morph; eauto. 2:reflexivity.
            split; try reflexivity. rewrite <-Hsel2; reflexivity.
          * subst. eapply Forall_forall; intros ? Hin. simpl_In.
            destruct (_ ==b _) eqn:Heq; inv Hf; rewrite equiv_decb_equiv in Heq; inv Heq.
            constructor.
          * simpl_Forall. constructor.
          * eapply wc_scope_incl; [| |eauto|].
            1,2:intros * Hin.
            -- eapply H18 in Hin as (Hck&?); subst.
               inv Hck. econstructor; solve_In; auto. simpl. rewrite equiv_decb_refl; eauto. auto.
            -- assert (exists ck, HasClock Γ'0 x ck) as (?&Hck) by (inv Hin; eauto with senv).
               eapply H18 in Hck as (Hck&?); subst.
               eapply H19 in Hin as Hil; subst.
               inv Hil. inv Hck. eapply NoDupMembers_det in H14; eauto; subst.
               econstructor; solve_In; auto. simpl. rewrite equiv_decb_refl; eauto. auto.
            -- intros; simpl in *; destruct_conjs; split; simpl_Forall; eauto using wc_block_incl.
               split; eauto using wc_exp_incl.
          * eapply sem_scope_ck'_refines3. 2-5:eauto.
            etransitivity; eauto.
          * intros; simpl in *; simpl_Forall; inv_VarsDefined; eauto.
            eapply sem_block_ck'_refines; eauto.
            eapply NoDupLocals_incl; [|eauto]. etransitivity; eauto. take (Permutation _ _) and rewrite <-it; eauto using incl_concat.
          * intros; simpl in *; simpl_Forall; inv_VarsDefined.
            eapply sem_block_ck'_restrict; eauto.
            eapply NoDupLocals_incl; [|eauto]. do 2 (etransitivity; eauto). take (Permutation _ _) and rewrite <-it; eauto using incl_concat.
          * intros; simpl in *; simpl_Forall; inv_VarsDefined.
            destruct Hi. eapply Forall_sem_block_dom_lb; eauto; simpl_Forall; eauto using NoDupLocals_incl, sem_block_ck'_sem_block.
          * intros; simpl in *.
            simpl_Forall. inv_VarsDefined.
            eapply H with (Γty:=Γty0); eauto using NoDup_locals_inv.
            -- etransitivity; eauto. take (Permutation _ _) and rewrite <-it; eauto using incl_concat.
            -- etransitivity; eauto. rewrite 2 map_app. apply incl_appr'. intros ??; solve_In.

      - (* locals *)
        constructor.
        eapply sem_scope_sem_scope_ck with (Γty:=Γty); eauto.
        + intros; simpl in *. simpl_Forall. inv_VarsDefined.
          eapply sem_block_ck'_refines; eauto.
          eapply NoDupLocals_incl; [|eauto]. etransitivity; eauto. rewrite <-H12; eauto using incl_concat.
        + intros; simpl in *. simpl_Forall. inv_VarsDefined.
          eapply sem_block_ck'_restrict; eauto.
          eapply NoDupLocals_incl; [|eauto]. do 2 (etransitivity; eauto). rewrite <-H14; eauto using incl_concat.
        + intros; simpl in *. inv_VarsDefined.
          destruct Hi.
          eapply Forall_sem_block_dom_lb; eauto;
            simpl_Forall; eauto using NoDupLocals_incl, sem_block_ck'_sem_block.
        + intros; simpl in *. simpl_Forall. inv_VarsDefined.
          eapply H with (Γty:=Γty0); eauto.
          * eapply NoDup_locals_inv; eauto.
          * etransitivity; eauto.
            rewrite <-H22; eauto using incl_concat.
          * etransitivity; eauto.
            rewrite 2 map_app. apply incl_appr'.
            intros ??; solve_In.
    Qed.

  End sem_ck.

  Theorem sem_node_sem_node_ck {PSyn prefs} :
    forall (G : @global PSyn prefs),
      wt_global G ->
      wc_global G ->
      Forall node_causal (nodes G) ->
      forall f ins outs,
        Sem.sem_node G f ins outs ->
        sem_clock_inputs G f ins ->
        sem_node_ck G f ins outs.
  Proof with eauto.
    intros (types&nodes) Hwt Hwc.
    assert (Ordered_nodes (Global types nodes)) as Hord by (eauto using wl_global_Ordered_nodes with ltyping).
    revert Hwc Hord.
    induction nodes; intros Hwc Hord Hcaus ??? Hsem Hckins. now inversion Hsem.
    assert (Hsem' := Hsem).
    inversion_clear Hsem' as [? ? ? ? ? ? Hfind Hins Houts Heqs Hbk].
    pose proof (Lord.find_node_not_Is_node_in _ _ _ Hord Hfind) as Hnini.
    simpl in Hfind. destruct (ident_eq_dec (n_name a) f).
    - destruct Hckins as (?&?&Hfind'&Hins'&Hscin).
      rewrite find_node_now in Hfind'; auto. inv Hfind'.
      rewrite find_node_now in Hfind; auto. inv Hfind.
      eapply Sem.sem_block_cons1 in Heqs; eauto.
      assert (Hord':=Hord). inversion_clear Hord' as [|? ? Hord'' Hnneqs Hnn].
      inversion_clear Hwc as [|?? (Hwcn&_) Hwcg].
      inv Hcaus.
      assert (Hwcn':=Hwcn). destruct Hwcn' as (?&?&?).

      (* sem_clock H0 -> sem_clock H *)
      eapply sem_clocks_det' in Hscin; eauto. clear x Hins'.

      (* restrict H *)
      eapply sem_node_restrict in Heqs as (Hdom&Hins'&Houts'&Heqs'); eauto.
      remember (FEnv.restrict H (idents (n_in n ++ n_out n))) as H'.
      eapply sem_clocks_det with (ins:=n_out n) in Hscin; eauto. 2:rewrite Permutation_app_comm; eauto.
      clear H HeqH' Hins Houts.

      (* sc_vars H *)
      assert (wc_global (Global types nodes0)) as Hvars by eauto.
      eapply sem_node_sc_vars in Hvars as (Hvars&Hloc); eauto.
      2:{ intros. eapply IHnodes; eauto. inv Hwt. inv H7. constructor; auto. }
      2:{ inv Hwt; inv H5; destruct H8; auto. }
      2:{ eapply sc_var_inv_intro; eauto. }

      (* sem_node_ck *)
      pose proof (n_defd n) as (?&Hdef&Hperm).
      eapply sem_block_sem_block_ck in Hloc; eauto; auto with datatypes.
      eapply Snode with (H:=H'); eauto.
      + rewrite find_node_now; auto.
      + eapply sem_block_ck_cons'; eauto.
      + unfold clocked_node. split; auto.
        rewrite map_fst_senv_of_inout; auto.
      + intros. eapply IHnodes; eauto. inv Hwt; inv H7; constructor; auto.
      + rewrite fst_NoDupMembers, map_fst_senv_of_inout, <-fst_NoDupMembers. apply n_nodup.
      + rewrite fst_NoDupMembers, map_fst_senv_of_inout, <-fst_NoDupMembers. apply n_nodup.
      + simpl. destruct H2 as (Hnd&_). rewrite idcaus_of_senv_inout. auto.
      + rewrite map_fst_senv_of_inout. apply n_nodup.
      + rewrite map_fst_senv_of_inout, Hperm. solve_incl_app.
      + simpl. rewrite idcaus_of_senv_inout. reflexivity.
      + rewrite map_fst_senv_of_inout; auto.
      + inv Hwt; inv H5; destruct H8 as ((?&?&?&?)&_); auto.
      + unfold senv_of_inout. simpl_app.
        erewrite 2 map_map, map_ext, map_ext with (l:=n_out n); eauto.
        1,2:intros; destruct_conjs; auto.
      + simpl_Forall. simpl_In. eapply Forall_forall in H1; [|solve_In]. simpl in *.
        unfold idck, senv_of_inout. erewrite map_map, map_ext; eauto.
        intros; destruct_conjs; auto.

    - rewrite find_node_other in Hfind; eauto.
      eapply Sem.sem_node_cons1 in Hsem; auto.
      assert (Hord':=Hord). rewrite cons_is_app in Hord'.
      inv Hord'. inv Hwt; inv H1. inv Hwc. inv Hcaus. eapply IHnodes in Hsem; eauto.
      eapply sem_node_ck_cons'; eauto.
      constructor; auto.
      eapply sem_clock_inputs_cons; eauto.
  Qed.

End LCLOCKCORRECTNESS.

Module LClockCorrectnessFun
       (Ids : IDS)
       (Op : OPERATORS)
       (OpAux : OPERATORS_AUX Ids Op)
       (Cks : CLOCKS Ids Op OpAux)
       (Senv  : STATICENV Ids Op OpAux Cks)
       (Syn : LSYNTAX Ids Op OpAux Cks Senv)
       (Typ : LTYPING Ids Op OpAux Cks Senv Syn)
       (Clo : LCLOCKING Ids Op OpAux Cks Senv Syn)
       (LCA : LCAUSALITY Ids Op OpAux Cks Senv Syn)
       (Lord : LORDERED Ids Op OpAux Cks Senv Syn)
       (CStr : COINDSTREAMS Ids Op OpAux Cks)
       (Sem : LSEMANTICS Ids Op OpAux Cks Senv Syn Lord CStr)
       (CkSem : LCLOCKEDSEMANTICS Ids Op OpAux Cks Senv Syn Clo Lord CStr Sem)
<: LCLOCKCORRECTNESS Ids Op OpAux Cks Senv Syn Typ Clo LCA Lord CStr Sem CkSem.
  Include LCLOCKCORRECTNESS Ids Op OpAux Cks Senv Syn Typ Clo LCA Lord CStr Sem CkSem.
End LClockCorrectnessFun.
