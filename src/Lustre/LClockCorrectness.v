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
    forall types externs (nodes : list (@node PSyn prefs)) f n ins,
      n_name n <> f ->
      sem_clock_inputs (Global types externs nodes) f ins <-> sem_clock_inputs (Global types externs (n :: nodes)) f ins.
  Proof.
    intros * Hname.
    split; intros (H & n' & Hfind &?&?);
      exists H, n'; repeat split; auto.
    - rewrite find_node_other; eauto.
    - erewrite <- find_node_other; eauto.
  Qed.

  Lemma inputs_clocked_vars {PSyn prefs} :
    forall types externs (nodes : list (@node PSyn prefs)) n H f ins,
      sem_clock_inputs (Global types externs (n :: nodes)) f ins ->
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
      destruct H6 as (_&Hinv&_). eapply Hinv; eauto.
      econstructor; solve_In; eauto using in_or_app; eauto.
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
      - eapply Hinv1; eauto.
      - eapply Hinv2; eauto.
        inv Hca; econstructor; eauto. congruence.
    Qed.

    Lemma sc_var_inv_sc_vars : forall Γ H b,
        NoDupMembers Γ ->
        (* (forall x, IsVar Γ x -> exists v, sem_var (fst H) x v) -> *)
        (* (forall x, IsLast Γ x -> exists v, sem_var (snd H) x v) -> *)
        Forall (sc_var_inv Γ H b) (map snd (idcaus_of_senv Γ)) ->
        sc_vars Γ H b.
    Proof.
      intros * Hnd (* Hv1 Hv2  *)Hinv.
      unfold idcaus_of_senv in Hinv. rewrite map_app in Hinv.
      apply Forall_app in Hinv as (Hinv1&Hinv2).
      unfold sc_vars. split; intros * Hck; [|intros Hca].
      - inv Hck. simpl_Forall.
        eapply Hinv1; eauto with senv.
      - inv Hck. inv Hca. eapply NoDupMembers_det in H0; eauto; subst.
        destruct (causl_last _) eqn:Hcaus; try congruence.
        eapply Forall_forall in Hinv2 as (_&Hinv2). 2:solve_In; rewrite Hcaus; simpl; eauto.
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

    Lemma sc_exp_extcall : forall Γ Γty H b f es ann,
       (forall k, k < length (annots es) -> P_exps (sc_exp_inv Γ Γty H b) es k) ->
       sc_exp_inv Γ Γty H b (Eextcall f es ann) 0.
    Proof.
      intros * Hes ? Hwt Hwc Hsem; inv Hwt; inv Hwc; inv Hsem; simpl.
      eapply P_exps_sc_exp_inv_all in Hes; eauto.
      take (liftn _ _ _) and apply ac_liftn in it.
      destruct (clocksof es); try congruence; simpl_Forall; simpl_In; simpl_Forall.
      destruct (concat ss0); inv Hes. simpl_Forall.
      take (_ ≡ _) and rewrite <-it; auto.
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
      - apply sc_exp_extcall; auto.
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
        | Sckscope : forall Γ Hi Hi' Hl Hl' bs locs blks,
            (forall x, FEnv.In x Hi' <-> IsVar (senv_of_locs locs) x) ->
            (forall x, FEnv.In x Hl' <-> IsLast (senv_of_locs locs) x) ->

            (forall x ty ck cx e0 clx,
                In (x, (ty, ck, cx, Some (e0, clx))) locs ->
                exists vs0 vs1 vs,
                  sem_exp G (Hi + Hi', Hl + Hl') bs e0 [vs0] /\ sem_var Hi' x vs1 /\ fby vs0 vs1 vs /\ sem_var Hl' x vs) ->

            sem_block (Γ ++ senv_of_locs locs) (Hi + Hi', Hl + Hl') blks ->

            Forall (fun x => sc_var_inv (senv_of_locs locs) (Hi + Hi', Hl + Hl') bs x) envS ->
            sem_scope_ck' envS Γ (Hi, Hl) bs (Scope locs blks).
      End sem_scope.

      Section sem_scope.

        Context {A : Type}.

        Variable sem_block : static_env -> A -> Prop.

        Inductive sem_branch_ck' (envS : list ident) : static_env -> Sem.history -> Stream bool -> (branch A) -> Prop :=
        | Sckbranch : forall Γ Hi Hl bs caus blks,
            sem_block (replace_idcaus caus Γ) blks ->
            Forall (fun cx => forall x ck vs, In (x, cx) caus -> HasClock Γ x ck -> sem_var Hi x vs -> sem_clock Hi bs ck (abstract_clock vs)) envS ->
            sem_branch_ck' envS Γ (Hi, Hl) bs (Branch caus blks).
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
                    exists Hi', Sem.when_hist (fst blks) Hi sc Hi'
                           /\ let bi := fwhenb (fst blks) sc b in
                             sem_branch_ck' (fun Γ => Forall (sem_block_ck' envP Γ Hi' bi))
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
                                  sem_branch_ck'
                                    (fun Γ scope =>
                                       sem_scope_ck' (fun Γ Hi' blks =>
                                                        Forall (sem_block_ck' envP Γ Hi' bik) (fst blks)
                                                        /\ sem_transitions G Hi' bik (snd blks) (tag, false) (fselect absent (tag) k stres stres1)
                                         ) envP Γ Hik bik (snd scope))
                                    envP (map (fun '(x, a) => (x, ann_with_clock a Cbase)) Γ) Hik bik (snd state)) states ->
          sem_block_ck' envP Γ H bs (Bauto Weak ck (ini, oth) states)
      | SckautoStrong:
        forall Γ H bs ini states ck bs' stres stres1,
          sem_clock (fst H) bs ck bs' ->
          fby (const_stres bs' (ini, false)) stres1 stres ->
          Forall (fun state =>
                    let tag := fst (fst state) in
                    forall k, exists Hik, Sem.select_hist tag k stres H Hik
                                /\ let bik := fselectb tag k stres bs in
                                  sem_branch (fun scope => sem_transitions G Hik bik (fst scope) (tag, false) (fselect absent (tag) k stres stres1))
                                             (snd state)
                 ) states ->
          Forall (fun state =>
                    let tag := fst (fst state) in
                    forall k, exists Hik, Sem.select_hist tag k stres1 H Hik
                                /\ let bik := fselectb tag k stres1 bs in
                                  sem_branch_ck'
                                    (fun Γ scope =>
                                       sem_scope_ck' (fun Γ Hi' blks => Forall (sem_block_ck' envP Γ Hi' bik) (fst blks)
                                         ) envP Γ Hik bik (snd scope))
                                    envP (map (fun '(x, a) => (x, ann_with_clock a Cbase)) Γ) Hik bik (snd state)
                 ) states ->
          sem_block_ck' envP Γ H bs (Bauto Strong ck ([], ini) states)
      | Scklocal:
        forall Γ Hi bs scope,
          sem_scope_ck' (fun Γ Hi' => Forall (sem_block_ck' envP Γ Hi' bs)) envP Γ Hi bs scope ->
          sem_block_ck' envP Γ Hi bs (Blocal scope).

    End sem_block_ck'.

    Ltac inv_branch :=
      match goal with
      | H:sem_branch_ck' _ _ _ _ _ _ |- _ => inv H; destruct_conjs; subst
      | _ => (Syn.inv_branch || Typ.inv_branch || Clo.inv_branch || Sem.inv_branch)
      end.

    Ltac inv_scope :=
      match goal with
      | H:sem_scope_ck' _ _ _ _ _ _ |- _ => inv H; destruct_conjs; subst
      | _ => (Syn.inv_scope || Typ.inv_scope || Clo.inv_scope || Sem.inv_scope || CkSem.inv_scope)
      end.

    Ltac inv_block :=
      match goal with
      | H:sem_block_ck' _ _ _ _ _ |- _ => inv H
      | _ => (Syn.inv_block || Typ.inv_block || Clo.inv_block || Sem.inv_block || CkSem.inv_block)
      end.

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
        repeat inv_branch. econstructor; eauto. simpl_Forall; eauto.
      - (* automaton (weak) *)
        econstructor; eauto.
        simpl_Forall. specialize (H10 k); destruct_conjs.
        do 2 esplit; eauto.
        repeat inv_branch. repeat inv_scope.
        do 2 econstructor; eauto. destruct_conjs; split; simpl_Forall; eauto.
      - (* automaton (strong) *)
        econstructor; eauto.
        simpl_Forall. specialize (H10 k); destruct_conjs.
        do 2 esplit; eauto.
        repeat inv_branch. repeat inv_scope.
        do 2 econstructor; eauto. simpl_Forall; eauto.
      - (* locals *)
        constructor.
        repeat inv_scope; econstructor; eauto.
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
        inv_branch; econstructor; eauto. simpl_Forall; eauto.
      - (* automaton (weak) *)
        econstructor; eauto.
        simpl_Forall. specialize (H11 k); destruct_conjs.
        do 2 esplit; eauto.
        repeat inv_branch. repeat inv_scope.
        do 2 econstructor; eauto. destruct_conjs; split; simpl_Forall; eauto.
      - (* automaton (strong) *)
        econstructor; eauto.
        simpl_Forall. specialize (H11 k); destruct_conjs.
        do 2 esplit; eauto.
        repeat inv_branch. repeat inv_scope.
        do 2 econstructor; eauto. simpl_Forall; eauto.
      - (* locals *)
        constructor.
        repeat inv_scope. econstructor; eauto.
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
        repeat inv_branch. econstructor; eauto.
        simpl_Forall; eauto.
        setoid_rewrite <-Hperm; auto.
      - (* automaton (weak) *)
        econstructor; eauto.
        simpl_Forall. specialize (H11 k); destruct_conjs.
        do 2 esplit; eauto. repeat inv_branch; repeat inv_scope. econstructor; [econstructor|]; eauto.
        split; simpl_Forall; eauto.
        1,2:setoid_rewrite <-Hperm; auto.
      - (* automaton (strong) *)
        econstructor; eauto.
        simpl_Forall. specialize (H11 k); destruct_conjs.
        do 2 esplit; eauto. repeat inv_branch; repeat inv_scope. econstructor; [econstructor|]; eauto.
        simpl_Forall; eauto.
        1,2:setoid_rewrite <-Hperm; auto.
      - (* local *)
        constructor.
        inv H4. econstructor; eauto.
        simpl_Forall; eauto.
        setoid_rewrite <-Hperm; auto.
    Qed.

    Lemma sc_var_inv_unwhen : forall Γ Γ' tx tn sc Hi bs x,
        0 < length tn ->
        wt_stream sc (Tenum tx tn) ->
        (forall y ck, HasCaus Γ y x -> HasClock Γ y ck -> HasCaus Γ' y x /\ HasClock Γ' y Cbase) ->
        (forall y ck, HasCaus Γ y x -> HasClock Γ y ck -> sem_clock (fst Hi) bs ck (abstract_clock sc)) ->
        (forall c, In c (seq 0 (length tn)) ->
              exists Hi',
                (forall y, HasCaus Γ y x -> FEnv.In y (fst Hi'))
                /\ Sem.when_hist c Hi sc Hi'
                /\ sc_var_inv Γ' Hi' (fwhenb c sc bs) x) ->
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
        + edestruct Hsc with (c:=0) as ((Hi'&?)&Hin&(Hwhen&_)&(Hsc'&_)). apply in_seq; lia.
          assert (exists vs, sem_var Hi' x0 vs) as (?&Hv').
          { edestruct Hin as (?&?); eauto. do 2 esplit; eauto. reflexivity. }
          eapply sem_var_when_inv in Hv' as (?&?&Hwhen'); eauto.
          eapply sem_var_det in Hv; eauto. rewrite <-Hv.
          eapply when_spec with (n:=n) in Hwhen' as [|[|]]; destruct_conjs; try congruence.
          take (sc # n = _) and setoid_rewrite it.
          take (x2 # n = _) and setoid_rewrite it. auto.
        + inv Hwt. edestruct Hsc with (c:=v0) as ((Hi'&?)&Hin&(Hwhen&_)&(Hsc'&_)). apply in_seq; lia.
          assert (exists vs, sem_var Hi' x0 vs) as (?&Hv').
          { edestruct Hin as (?&?); eauto. do 2 esplit; eauto. reflexivity. }
          assert (Hvx:=Hv'). eapply sem_var_when_inv in Hvx as (?&?&Hwhen'); eauto.
          eapply sem_var_det in Hv; eauto. rewrite <-Hv.
          edestruct Hwc as (Hca'&Hck'); eauto. eapply Hsc' in Hv'; eauto.
          eapply sem_clock_equiv in Hsemck. specialize (Hsemck n). rewrite 2 tr_Stream_nth, ac_nth in Hsemck.
          eapply sem_clock_equiv in Hv'. specialize (Hv' n). rewrite 2 tr_Stream_nth, ac_nth, fwhenb_nth in Hv'.
          eapply when_spec with (n:=n) in Hwhen' as [|[|]]; destruct_conjs; try congruence.
          take (sc # n = _) and setoid_rewrite it.
          take (x2 # n = _) and setoid_rewrite it. auto.
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
        + edestruct Hsc with (c:=0) as ((Hi'&?)&Hin&(Hwhen&_)&(Hsc'&_)). apply in_seq; lia.
          assert (exists vs, sem_var Hi' x0 vs) as (?&Hv').
          { edestruct Hin as (?&?); eauto. do 2 esplit; eauto. reflexivity. }
          eapply sem_var_select_inv with (k:=(count (fwhenb 0 (stres_st sc) (stres_res sc))) # n) in Hv' as (?&?&Hwhen'); eauto.
          eapply sem_var_det in Hv; eauto. rewrite <-Hv.
          apply select_mask_when in Hwhen' as (?&Hfil&Hmask).
          eapply when_spec with (n:=n) in Hfil as [|[|]]; destruct_conjs; try rewrite Hx; auto.
          all:take ((stres_st _) # _ = _) and setoid_rewrite Str_nth_map in it; setoid_rewrite Hscn in it; try congruence.
          take (x2 # _ = _) and setoid_rewrite it. auto.
        + edestruct Hsc with (c:=n0) as ((Hi'&?)&Hin&(Hwhen&_)&(Hsc'&_)). apply in_seq; lia.
          assert (exists vs, sem_var Hi' x0 vs) as (?&Hv').
          { edestruct Hin as (?&?); eauto. do 2 esplit; eauto. reflexivity. }
          assert (Hvx:=Hv'). eapply sem_var_select_inv with (k:=(count (fwhenb n0 (stres_st sc) (stres_res sc))) # n) in Hvx as (?&?&Hwhen'); eauto.
          eapply sem_var_det in Hv; eauto. rewrite <-Hv.
          edestruct Hwc as (Hca'&Hck'); eauto. eapply Hsc' in Hv'; eauto.
          eapply sem_clock_equiv in Hsemck. specialize (Hsemck n). rewrite 2 tr_Stream_nth, ac_nth in Hsemck.
          eapply sem_clock_equiv in Hv'. specialize (Hv' n).
          unfold fselectb, fselect in Hv'. rewrite 2 tr_Stream_nth, ac_nth, mask_nth, Nat.eqb_refl, fwhen_nth in Hv'.
          setoid_rewrite Str_nth_map in Hv'. setoid_rewrite Hscn in Hv'. rewrite equiv_decb_refl in Hv'. inv Hv'.
          apply select_mask_when in Hwhen' as (ys&Hfil&Hmask).
          apply eqst_ntheq with (n:=n) in Hmask. unfold maskv in Hmask. rewrite mask_nth, Nat.eqb_refl in Hmask.
          eapply when_spec with (n:=n) in Hfil as [|[|]]; destruct_conjs.
          all:take ((stres_st _) # _ = _) and setoid_rewrite Str_nth_map in it; setoid_rewrite Hscn in it; try congruence.
          take (x2 # n = _) and setoid_rewrite it. auto.
      - exfalso. eapply Hnin; eauto.
    Qed.

    Lemma sc_var_inv_local :
      forall Γ (locs : list (ident * (type * clock * ident * option (exp * ident)))) Hi Hl Hi' Hl' bs cx,
        (forall x, InMembers x locs -> ~In x (map fst Γ)) ->
        FEnv.dom_ub Hi (map fst Γ) ->
        FEnv.dom_ub Hl (map fst Γ) ->
        (forall x, FEnv.In x Hi' <-> IsVar (senv_of_locs locs) x) ->
        (forall x, FEnv.In x Hl' <-> IsLast (senv_of_locs locs) x) ->
        (forall x, HasCaus Γ x cx \/ HasLastCaus Γ x cx -> sc_var_inv Γ (Hi, Hl) bs cx) ->
        (forall x, HasCaus (senv_of_locs locs) x cx \/ HasLastCaus (senv_of_locs locs) x cx ->
              sc_var_inv (senv_of_locs locs) (Hi + Hi', Hl + Hl') bs cx) ->
        sc_var_inv (Γ ++ senv_of_locs locs) (Hi + Hi', Hl + Hl') bs cx.
    Proof.
      intros * Hnd Hdomub Hdomubl Hdom Hdoml Hsc1 Hsc2.
      assert (FEnv.refines (@EqSt _) Hi (Hi + Hi')) as Href.
      { intros ?? Hfind. do 2 esplit; try reflexivity.
        apply FEnv.union2; auto.
        rewrite <-FEnv.not_find_In, Hdom, IsVar_senv_of_locs.
        intro contra. eapply Hnd, Hdomub; eauto. econstructor; eauto. }
      assert (FEnv.refines (@EqSt _) Hl (Hl + Hl')) as Hrefl.
      { intros ?? Hfind. do 2 esplit; try reflexivity.
        apply FEnv.union2; auto.
        rewrite <-FEnv.not_find_In, Hdoml.
        intro contra. apply IsLast_senv_of_locs in contra.
        eapply Hnd, Hdomubl; eauto. econstructor; eauto. }
      split; intros ??? Hca Hck Hv;
        rewrite HasClock_app in Hck; (rewrite HasCaus_app in Hca||rewrite HasLastCaus_app in Hca);
        destruct Hck as [Hck|Hck]; try rewrite replace_idcaus_HasClock in Hck.
      - destruct Hca as [Hca|Hca].
        2:{ exfalso. inv Hca. inv Hck. simpl_In.
            eapply Hnd; eauto using In_InMembers. solve_In. }
        eapply sem_clock_refines; eauto.
        edestruct Hsc1 as (Hsc&_); eauto. eapply Hsc; eauto.
        eapply sem_var_refines'; eauto.
        apply sem_var_In, FEnv.union_In in Hv as [Hv|Hv]; auto. exfalso.
        apply Hdom, IsVar_senv_of_locs in Hv.
        eapply Hnd; eauto. inv Hca; solve_In.
      - destruct Hca as [Hca|Hca].
        1:{ exfalso. inv Hca. inv Hck. simpl_In.
            eapply Hnd; eauto using In_InMembers. solve_In. }
        edestruct Hsc2 as (Hsc&_); eauto.
      - destruct Hca as [Hca|Hca].
        2:{ exfalso. inv Hca. inv Hck. simpl_In.
            eapply Hnd; eauto using In_InMembers. solve_In. }
        eapply sem_clock_refines; eauto.
        edestruct Hsc1 as (_&Hsc); eauto. eapply Hsc; eauto.
        eapply sem_var_refines'; eauto.
        apply sem_var_In, FEnv.union_In in Hv as [Hv|Hv]; auto. exfalso.
        apply Hdoml, IsLast_senv_of_locs in Hv.
        eapply Hnd; eauto. inv Hca; solve_In.
      - destruct Hca as [Hca|Hca].
        1:{ exfalso. inv Hca. inv Hck. simpl_In.
            eapply Hnd; eauto using In_InMembers. solve_In. }
        edestruct Hsc2 as (_&sc); eauto.
    Qed.

    Lemma sc_var_inv_branch :
      forall Γ caus Hi Hl bs cx,
        (forall x, HasCaus Γ x cx \/ HasLastCaus Γ x cx -> sc_var_inv Γ (Hi, Hl) bs cx) ->
        (forall x ck vs, In (x, cx) caus -> HasClock Γ x ck -> sem_var Hi x vs ->
                    sem_clock Hi bs ck (abstract_clock vs)) ->
        sc_var_inv (replace_idcaus caus Γ) (Hi, Hl) bs cx.
    Proof.
      intros * Hsc1 Hsc2.
      split; intros ??? Hca Hck Hv; try rewrite replace_idcaus_HasClock in Hck.
      - apply replace_idcaus_HasCaus3 in Hca as [Hca|Hca].
        + edestruct Hsc1 as (Hinv&_); eauto.
        + simpl in *. eapply Hsc2; eauto.
      - rewrite replace_idcaus_HasLastCaus in Hca.
        edestruct Hsc1 as (_&Hinv); eauto.
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
      forall envS locs (blks: A) Γ Γty xs Hi bs cy,
        wc_global G ->
        NoDup (map snd (idcaus_of_senv Γ ++ idcaus_of_scope f_idcaus (Scope locs blks))) ->
        NoDupMembers Γ ->
        NoDupScope P_nd (map fst Γ) (Scope locs blks) ->
        VarsDefinedScope P_vd (Scope locs blks) xs ->
        incl xs (map fst Γ) ->
        wt_scope P_wt G Γty (Scope locs blks) ->
        wc_env (idck Γ) ->
        wc_scope P_wc G Γ (Scope locs blks) ->
        sem_scope_ck' P_blk1 envS Γ Hi bs (Scope locs blks) ->
        FEnv.dom_ub (fst Hi) (map fst Γ) ->
        FEnv.dom_ub (snd Hi) (map fst Γ) ->
        (forall x cx, HasCaus Γ x cx \/ HasLastCaus Γ x cx ->
                 depends_on_scope P_dep Γ cy cx (Scope locs blks) -> sc_var_inv Γ Hi bs cx) ->
        (forall cx, In cx (map snd (idcaus_of_scope f_idcaus (Scope locs blks))) ->
               depends_on_scope P_dep Γ cy cx (Scope locs blks) -> In cx envS) ->
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
            FEnv.dom_ub (snd Hi) (map fst Γ) ->
            (forall x cx, HasCaus Γ x cx \/ HasLastCaus Γ x cx ->
                     P_dep Γ cy cx blks -> sc_var_inv Γ Hi bs cx) ->
            (forall cx, In cx (map snd (f_idcaus blks)) ->
                   P_dep Γ cy cx blks -> In cx envS) ->
            (forall y, In y xs -> HasCaus Γ y cy -> sc_var_inv Γ Hi bs cy)
            /\ P_blk2 Γ Hi blks) ->
        (forall y, In y xs -> HasCaus Γ y cy -> sc_var_inv Γ Hi bs cy)
        /\ sem_scope_ck' P_blk2 (cy::envS) Γ Hi bs (Scope locs blks).
    Proof.
      intros * HwcG Hnd1 Hnd2 Hnd4 Hvars Hincl Hwt Henv Hwc Hsem Hdom Hdoml Hsc HenvP Hind;
        inv Hnd4; inv Hvars; inv Hwt; inv Hwc; inv Hsem; simpl in *.

      assert (FEnv.refines (@EqSt _) Hi0 (Hi0 + Hi')) as Href1.
      { intros ?? Hfind. do 2 esplit; try reflexivity.
        apply FEnv.union2; auto.
        rewrite <-FEnv.not_find_In, H2, IsVar_senv_of_locs.
        intro contra. eapply H4, Hdom; eauto. econstructor; eauto. }

      assert (forall x cx,
                 HasCaus (Γ ++ senv_of_locs locs) x cx \/ HasLastCaus (Γ ++ senv_of_locs locs) x cx ->
                 depends_on_scope P_dep Γ cy cx (Scope locs blks) ->
                 sc_var_inv (Γ ++ senv_of_locs locs) (Hi0 + Hi', Hl + Hl') bs cx
             ) as Hscloc.
      { intros * _ Hdep. eapply sc_var_inv_local; eauto.
        intros * Hca. apply idcaus_of_senv_In in Hca.
        eapply Forall_forall in H19; eauto. eapply HenvP; eauto.
        rewrite map_app, in_app_iff. left. solve_In.
      }

      assert (wc_env (idck (Γ ++ senv_of_locs locs))) as Hwenv'.
      { simpl_app. apply wc_env_app; auto.
        - simpl_Forall. eauto. }

      edestruct Hind with (Hi:=(Hi0 + Hi', Hl + Hl'))
                          (Γ:=Γ ++ senv_of_locs locs) as (Hsc'&Hcons); eauto using in_or_app.
      1:{ rewrite idcaus_of_senv_app, <-app_assoc.
          eapply Permutation_NoDup; [|eauto]. solve_Permutation_app. }
      1:{ apply NoDupMembers_app; auto.
          - now apply NoDupMembers_senv_of_locs.
          - intros. rewrite InMembers_senv_of_locs. intros ?.
            eapply H4, fst_InMembers; eauto. }
      1:{ now rewrite map_app, map_fst_senv_of_locs. }
      1:{ rewrite map_app, map_fst_senv_of_locs.
          apply incl_appl'; auto. }
      1:{ apply FEnv.union_dom_ub; auto. 1,2:eapply FEnv.dom_ub_incl; [|eauto].
          3:intros ? Henvin; rewrite H2, IsVar_senv_of_locs, fst_InMembers in Henvin; eauto.
          1,2:solve_incl_app. erewrite map_map, map_ext; [reflexivity|].
          intros; destruct_conjs; auto. }
      1:{ apply FEnv.union_dom_ub; auto. 1,2:eapply FEnv.dom_ub_incl; [|eauto].
          3:intros ? Henvin; apply H11, IsLast_senv_of_locs, fst_InMembers in Henvin; eauto.
          1,2:solve_incl_app. erewrite map_map, map_ext; [reflexivity|].
          intros; destruct_conjs; auto. }
      1:{ intros. eapply sc_var_inv_local; eauto.
          - intros. eapply Hsc; eauto. econstructor; solve_Exists.
          - intros * Hin. eapply Forall_forall in H19; eauto.
            apply idcaus_of_senv_In in Hin.
            eapply HenvP; eauto. rewrite map_app, in_app_iff; left. solve_In.
            econstructor; solve_Exists. }
      1:{ intros. eapply HenvP. rewrite map_app, in_app_iff; auto.
          econstructor; solve_Exists. }

      split.
      - intros * Hinxs Hca.
        split; intros ??? Hca' Hck Hv; simpl_In.
        + eapply HasCaus_snd_det in Hca; eauto; subst. 2:solve_NoDup_app.
          edestruct Hsc' as (Hsc1&_); eauto using in_or_app.
          apply HasCaus_app; auto using replace_idcaus_HasCaus2.
          eapply sem_var_refines, Hsc1 in Hv; eauto using in_or_app.
          2:rewrite HasCaus_app; auto using replace_idcaus_HasCaus2.
          2:rewrite HasClock_app; eauto.
          eapply sem_clock_refines_iff; eauto.
          intros * Hfree.
          eapply wc_clock_is_free_in in Hfree; [|eauto].
          2:{ eapply wc_env_var in Henv; eauto. inv Hck; solve_In. }
          apply InMembers_In in Hfree as (?&?); solve_In.
          intros Henvin. apply FEnv.union_In in Henvin as [Henvin|Henvin]; auto. exfalso.
          apply H2, IsVar_senv_of_locs in Henvin.
          eapply H4; eauto. solve_In.
        + exfalso. eapply NoDup_HasCaus_HasLastCaus; eauto. solve_NoDup_app.

      - econstructor. 4:eauto. all:eauto.
        constructor; auto.
        split; intros * Hca Hck Hv.
        + (* locs *)
          edestruct Hsc' as (Hsc1&_). 2:apply HasCaus_app; eauto.
          1:apply in_or_app, or_intror; inv Hca; solve_In.
          eapply Hsc1; eauto. apply HasCaus_app; eauto. apply HasClock_app; eauto.

        + (* lasts *)
          inv Hca. inv Hck. simpl_In. eapply NoDupMembers_det in Hin0; eauto; inv Hin0.
          simpl_Forall.
          edestruct H14 as (?&?&?&He&Hv1&Hfby&Hv2); eauto.
          eapply sem_var_refines, sem_var_det in Hv2; [|apply Hv|apply FEnv.union_refines4']; eauto using EqStrel_Reflexive. rewrite Hv2.
          { eapply sc_exp' with (Γ:=Γ++senv_of_locs locs) (k:=0) in He; eauto with lclocking; simpl in *.
            - take (clockof e = _) and setoid_rewrite it in He; simpl in He.
              apply ac_fby1 in Hfby. now rewrite <-Hfby.
            - apply NoDupMembers_app; auto.
              + apply NoDupMembers_senv_of_locs; auto.
              + intros. rewrite InMembers_senv_of_locs. intros ?.
                eapply H4; eauto. solve_In.
            - rewrite <-length_clockof_numstreams, H0; auto.
            - intros ? Hfree. edestruct Is_free_left_In_snd; eauto.
              eapply Hscloc; eauto.
              eapply DepOnScope2; eauto. solve_Exists.
          }
    Qed.

    Lemma sc_branch {A} f_idcaus P_nd P_vd P_wt P_wc (P_blk1 P_blk2 : _ -> _ -> Prop) P_dep :
      forall envS caus (blks: A) Γ xs Hi bs cy,
        wc_global G ->
        NoDup (map snd (idcaus_of_senv Γ ++ idcaus_of_branch f_idcaus (Branch caus blks))) ->
        NoDupMembers Γ ->
        NoDupBranch P_nd (Branch caus blks) ->
        VarsDefinedBranch P_vd (Branch caus blks) xs ->
        incl xs (map fst Γ) ->
        wt_branch P_wt (Branch caus blks) ->
        wc_env (idck Γ) ->
        wc_branch P_wc (Branch caus blks) ->
        sem_branch_ck' P_blk1 envS Γ Hi bs (Branch caus blks) ->
        FEnv.dom_ub (fst Hi) (map fst Γ) ->
        FEnv.dom_ub (snd Hi) (map fst Γ) ->
        (forall x cx, HasCaus Γ x cx \/ HasLastCaus Γ x cx ->
                 depends_on_branch P_dep Γ cy cx (Branch caus blks) -> sc_var_inv Γ Hi bs cx) ->
        (forall cx, In cx (map snd (idcaus_of_branch f_idcaus (Branch caus blks))) ->
               depends_on_branch P_dep Γ cy cx (Branch caus blks) -> In cx envS) ->
        (let Γ := replace_idcaus caus Γ in
         NoDup (map snd (idcaus_of_senv Γ ++ f_idcaus blks)) ->
         NoDupMembers Γ ->
         P_nd blks ->
         P_vd blks xs ->
         incl xs (map fst Γ) ->
         P_wt blks ->
         wc_env (idck Γ) ->
         P_wc blks ->
         P_blk1 Γ blks ->
         FEnv.dom_ub (fst Hi) (map fst Γ) ->
         FEnv.dom_ub (snd Hi) (map fst Γ) ->
         (forall x cx, HasCaus Γ x cx \/ HasLastCaus Γ x cx ->
                  P_dep Γ cy cx blks -> sc_var_inv Γ Hi bs cx) ->
         (forall cx, In cx (map snd (f_idcaus blks)) ->
                P_dep Γ cy cx blks -> In cx envS) ->
         (forall y, In y xs -> HasCaus Γ y cy -> sc_var_inv Γ Hi bs cy)
         /\ P_blk2 Γ blks) ->
        (forall y, In y xs -> HasCaus Γ y cy -> sc_var_inv Γ Hi bs cy)
        /\ sem_branch_ck' P_blk2 (cy::envS) Γ Hi bs (Branch caus blks).
    Proof.
      intros * HwcG Hnd1 Hnd2 Hnd4 Hvars Hincl Hwt Henv Hwc Hsem Hdom Hdoml Hsc HenvP Hind;
        inv Hnd4; inv Hvars; inv Hwt; inv Hwc; inv Hsem; simpl in *.

      edestruct Hind as (Hsc'&Hcons). 9:eauto. all:eauto.
      1:{ apply replace_idcaus_NoDup; auto. }
      1:{ apply NoDupMembers_map; auto. }
      1:{ now rewrite map_fst_replace_idcaus. }
      1:{ unfold wc_env, idck in *. simpl_Forall. simpl_In. simpl_Forall.
          unfold replace_idcaus. erewrite map_map, map_ext. 2:intros; destruct_conjs; simpl.
          1,2:destruct (assoc_ident _ _); simpl; eauto. }
      1,2:now rewrite map_fst_replace_idcaus.
      1:{ intros * Hin Hdep. eapply sc_var_inv_branch; eauto.
          - intros. eapply Hsc; eauto. econstructor; solve_Exists.
          - intros. eapply Forall_forall in H11; eauto.
            eapply HenvP; eauto. rewrite map_app, in_app_iff. left; solve_In.
            econstructor; solve_Exists. }
      1:{ intros * Hin Hdep. eapply HenvP; eauto.
          - rewrite map_app; auto with datatypes.
          - econstructor; solve_Exists. }

      split.
      - intros * Hinxs Hca.
        split; intros ??? Hca' Hck Hv; simpl_In.
        + eapply HasCaus_snd_det in Hca; eauto; subst. 2:solve_NoDup_app.
          destruct (InMembers_dec y caus ident_eq_dec).
          * apply fst_InMembers in i; simpl_In.
            eapply Forall_forall in H11; eauto. eapply HenvP; eauto using DepOnBranch2.
            repeat rewrite map_app, in_app_iff. left; solve_In.
          * edestruct Hsc' as (Hsc1&_); eauto using replace_idcaus_HasCaus2.
            eapply Hsc1; eauto using replace_idcaus_HasCaus2.
            now rewrite replace_idcaus_HasClock.
        + exfalso. eapply NoDup_HasCaus_HasLastCaus; eauto. solve_NoDup_app.

      - econstructor; eauto. constructor; auto.
        intros * Hcaus Hck Hv.
        assert (exists cx, HasCaus Γ x cx) as (?&Hca) by (inv Hck; eauto with senv).
        edestruct Hsc' as (Hsc1&_). 3:eapply Hsc1; eauto.
        2,3:eapply replace_idcaus_HasCaus1; eauto.
        + apply H5. solve_In.
        + now rewrite replace_idcaus_HasClock.
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
        FEnv.dom_ub (snd Hi) (map fst Γ) ->
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
          - unfold Sem.mask_hist. eapply FEnv.dom_ub_map in Hdoml; eauto.
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
                            Sem.when_hist k Hi sc Hi'
                            /\ (forall y, In y xs -> HasCaus (map (fun '(x, e) => (x, ann_with_clock e Cbase)) Γ) y cy -> sc_var_inv (map (fun '(x, e) => (x, ann_with_clock e Cbase)) Γ) Hi' (fwhenb k sc bs) cy) /\
                              sem_branch_ck'
                                (fun Γ => Forall (sem_block_ck' (cy::envP) Γ Hi' (fwhenb k sc bs)))
                                (cy :: envP) (map (fun '(x, a) => (x, ann_with_clock a Cbase)) Γ) Hi' (fwhenb k sc bs) s)
                       branches) as Hf.
        { simpl_Forall. do 2 esplit; eauto.
          destruct b.
          eapply sc_branch
            with (P_dep:=fun Γ cx cy => Exists (depends_on Γ cx cy))
                 (Γ:=map (fun '(x, e) => (x, ann_with_clock e Cbase)) Γ) in H18 as (Hsc'&?); eauto.
          - clear - H0 Hnd1.
            eapply NoDup_locals_inv2; eauto.
            unfold idcaus_of_senv in *. erewrite map_map, map_filter_map, map_ext with (l:=Γ), map_filter_ext with (xs:=Γ); eauto.
            1,2:intros; destruct_conjs; auto.
          - apply NoDupMembers_map; auto.
          - erewrite map_map, map_ext; eauto. intros; destruct_conjs; auto.
          - apply Forall_forall; intros ? Hin. simpl_In. constructor.
          - destruct H1 as (Href&_). eapply FEnv.dom_ub_refines; eauto.
            erewrite map_map, map_ext; eauto. intros; destruct_conjs; auto.
          - destruct H1 as (_&Href). eapply FEnv.dom_ub_refines; eauto.
            erewrite map_map, map_ext; eauto. intros; destruct_conjs; auto.
          - intros * ? Hdep.
            split; intros ??? Hca Hck Hv; inv Hca; inv Hck; simpl_In.
            + destruct H1 as (Hwhen&_). eapply sem_var_when_inv in Hv as (?&Hv&Hwhen'); eauto.
              apply when_fwhen in Hwhen' as Heq. rewrite Heq in *. rewrite ac_fwhen.
              constructor.
              assert (depends_on Γ cy (causl a0) (Bswitch ec branches)) as Hdep2.
              { eapply depends_on_incl. 3:econstructor; solve_Exists.
                1,2:intros * Has; inv Has; simpl_In; eauto with senv. }
              eapply fwhenb_both_slower.
              * eapply sc_slower; eauto using ac_aligned. eapply Hsemck; eauto using depends_on_def_last.
              * apply ac_when in Hwhen'. rewrite Hwhen'.
                eauto using aligned_slower, ac_aligned.
            + destruct H1 as (_&Hwhen). eapply sem_var_when_inv in Hv as (?&Hv&Hwhen'); eauto.
              apply when_fwhen in Hwhen' as Heq. rewrite Heq in *. rewrite ac_fwhen.
              constructor.
              assert (depends_on Γ cy cx (Bswitch ec branches)) as Hdep2.
              { eapply depends_on_incl. 3:econstructor; solve_Exists.
                1,2:intros * Has; inv Has; simpl_In; eauto with senv. }
              eapply fwhenb_both_slower.
              * eapply sc_slower; eauto using ac_aligned. eapply Hsemck; eauto using depends_on_def_last.
              * apply ac_when in Hwhen'. rewrite Hwhen'.
                eauto using aligned_slower, ac_aligned.
          - intros ? Hin' Hdep. apply HenvP. solve_In.
            eapply depends_on_incl. 3:econstructor; solve_Exists.
            1,2:intros * Has; inv Has; simpl_In; eauto with senv.
          - intros; simpl in *; simpl_Forall.
            assert (Forall (fun blks => (forall y xs, VarsDefined blks xs -> In y xs -> HasCaus Γ0 y cy ->
                                              sc_var_inv Γ0 (h, h0) (fwhenb e sc bs) cy)
                                     /\ sem_block_ck' (cy::envP) Γ0 (h, h0) (fwhenb e sc bs) blks) l0) as Hf.
            { simpl_Forall. inv_VarsDefined.
              edestruct H with (Γ:=Γ0) (xs:=xs0). 10:eauto. all:eauto; subst Γ0.
              - eapply NoDup_locals_inv; eauto.
              - erewrite map_fst_replace_idcaus, map_map, map_ext; eauto.
                intros; destruct_conjs; auto.
              - etransitivity; eauto using incl_concat.
                take (Permutation _ _) and now rewrite it.
              - eapply wc_block_incl. 3:eauto.
                + intros * Hck. take (forall x ck, HasClock _ _ _ -> _) and apply it in Hck as (Hck&?); subst.
                  apply replace_idcaus_HasClock. inv Hck. econstructor.
                  solve_In. reflexivity.
                + intros * Hl. take (forall x, IsLast _ _ -> _) and apply it in Hl.
                  apply replace_idcaus_IsLast. inv Hl. econstructor.
                  solve_In. unfold ann_with_clock. auto.
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
          eapply sc_var_inv_unwhen with (tn:=tn) (Γ':=map (fun '(x, e) => (x, ann_with_clock e Cbase)) Γ); eauto.
          * destruct tn; simpl in *; try lia.
            apply Permutation_sym, Permutation_nil, map_eq_nil in H8; congruence.
          * rewrite H6 in H21; inv H21; eauto.
          * intros * Hca Hck.
            eapply HasCaus_snd_det in Hca1; eauto; [|simpl_app; eauto using NoDup_app_l]; subst.
            inv Hck. inv Hca.
            split; econstructor; solve_In; auto.
          * intros * Hca Hck.
            eapply HasCaus_snd_det in Hca1; eauto; [|simpl_app; eauto using NoDup_app_l]; subst.
            inv Hck. inv Hca. eapply NoDupMembers_det in H; eauto. subst.
            assert (clo e = ck) as Heq; try (rewrite Heq; eauto).
            inv Hdef. rename H14 into Hdef. simpl_Exists; simpl_Forall.
            repeat inv_branch. simpl_Exists. simpl_Forall.
            take (Syn.Is_defined_in _ _) and eapply wc_block_Is_defined_in in it; eauto.
            eapply InMembers_In in it as (?&Hin').
            take (forall x ck, HasClock _ _ _ -> _) and edestruct it as (Hck&_); eauto with senv.
            inv Hck. eapply NoDupMembers_det in H0; eauto. congruence.
          * intros * Hin. rewrite <-H8 in Hin. simpl_In; simpl_Forall.
            do 2 esplit; [|split; eauto].
            1:{ intros ? Hca.
                eapply HasCaus_snd_det in Hca1; eauto; [|simpl_app; eauto using NoDup_app_l]; subst.
                destruct b. eapply sem_branch_defined1; eauto.
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
          - apply NoDupMembers_map_filter; auto.
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
        assert (Forall (fun '((e, _), br) => forall k, exists Hi',
                            Sem.select_hist e k stres Hi Hi'
                            /\ (forall y, In y xs -> HasCaus (map (fun '(x, e) => (x, ann_with_clock e Cbase)) Γ) y cy ->
                                    sc_var_inv (map (fun '(x, e) => (x, ann_with_clock e Cbase)) Γ) Hi' (fselectb e k stres bs) cy)
                            /\ sem_branch_ck'
                                (fun Γ s => sem_scope_ck'
                                           (fun Γ Hi blks => Forall (sem_block_ck' (cy::envP) Γ Hi (fselectb e k stres bs)) (fst blks)
                                                          /\ sem_transitions G Hi (fselectb e k stres bs) (snd blks) (e, false) (fselect absent e k stres stres1))
                                           (cy :: envP) Γ Hi' (fselectb e k stres bs) (snd s))
                                (cy :: envP) (map (fun '(x, a) => (x, ann_with_clock a Cbase)) Γ) Hi' (fselectb e k stres bs) br)
                       states) as Hf.
        { simpl_Forall. intros. take (forall (k: nat), _) and specialize (it k); destruct_conjs. destruct b as [?(?&[?(?&?)])]; destruct_conjs.
          do 2 esplit; eauto.
          take (wt_branch _ _) and eapply sc_branch
            with (P_dep:=fun Γ cx cy blks => depends_on_scope (fun Γ cx cy blks => Exists (depends_on Γ cx cy) (fst blks)) Γ cx cy (snd blks))
                 (Γ:=map (fun '(x, e) => (x, ann_with_clock e Cbase)) Γ) in it as (Hsc'&?); eauto.
          - clear - H0 Hnd1.
            eapply NoDup_locals_inv2; eauto.
            unfold idcaus_of_senv in *. erewrite map_map, map_filter_map, map_ext with (l:=Γ), map_filter_ext with (xs:=Γ); eauto.
            1,2:intros; destruct_conjs; auto.
          - apply NoDupMembers_map; auto.
          - erewrite map_map, map_ext; eauto. intros; destruct_conjs; auto.
          - apply Forall_forall; intros ? Hin. simpl_In. constructor.
          - take (Sem.select_hist _ _ _ _ _) and destruct it as (Href&_). eapply FEnv.dom_ub_refines; eauto.
            erewrite map_map, map_ext; eauto. intros; destruct_conjs; auto.
          - take (Sem.select_hist _ _ _ _ _) and destruct it as (_&Href). eapply FEnv.dom_ub_refines; eauto.
            erewrite map_map, map_ext; eauto. intros; destruct_conjs; auto.
          - intros * ? Hdep.
            split; intros ??? Hca Hck Hv; inv Hca; inv Hck; simpl_In.
            + destruct H1 as (Hselect&_). eapply sem_var_select_inv in Hv as (?&Hv&Hselect'); eauto.
              apply select_fselect in Hselect' as Heq. rewrite Heq in *. rewrite ac_fselect.
              constructor.
              assert (depends_on Γ cy (causl a0) (Bauto Weak ck (ini0, oth) states)) as Hdep2.
              { eapply depends_on_incl. 3:econstructor; solve_Exists; inv Hdep; [eapply DepOnBranch1|eapply DepOnBranch2]; eauto.
                1,2:intros * Has; inv Has; simpl_In; eauto with senv. }
              eapply fselectb_both_slower.
              * take (sem_clock _ _ _ bs') and eapply sc_slower in it.
                2:rewrite Hac, <-stres_st_ac; eauto using depends_on_def_last, ac_aligned.
                eapply slower_ac_morph; [|eauto]. apply stres_st_ac.
              * apply ac_select in Hselect'. rewrite <-Hselect'.
                eauto using aligned_slower, ac_aligned.
            + destruct H1 as (_&Hselect). eapply sem_var_select_inv in Hv as (?&Hv&Hselect'); eauto.
              apply select_fselect in Hselect' as Heq. rewrite Heq in *. rewrite ac_fselect.
              constructor.
              assert (depends_on Γ cy cx (Bauto Weak ck (ini0, oth) states)) as Hdep2.
              { eapply depends_on_incl. 3:econstructor; solve_Exists; inv Hdep; [eapply DepOnBranch1|eapply DepOnBranch2]; eauto.
                1,2:intros * Has; inv Has; simpl_In; eauto with senv. }
              eapply fselectb_both_slower.
              * take (sem_clock _ _ _ bs') and eapply sc_slower in it.
                2:rewrite Hac, <-stres_st_ac; eauto using depends_on_def_last, ac_aligned.
                eapply slower_ac_morph; [|eauto]. apply stres_st_ac.
              * apply ac_select in Hselect'. rewrite <-Hselect'.
                eauto using aligned_slower, ac_aligned.
          - intros ? Hin' Hdep. apply HenvP. solve_In.
            eapply depends_on_incl. 3:econstructor; solve_Exists; inv Hdep; [eapply DepOnBranch1|eapply DepOnBranch2]; eauto.
            1,2:intros * Has; inv Has; simpl_In; eauto with senv.
          -{ intros; simpl in *. destruct_conjs.
             take (wt_scope _ _ _ _) and eapply sc_scope
               with (P_dep:=fun Γ cx cy blks => Exists (depends_on Γ cx cy) (fst blks))
                    (Γ:=Γ0) in it as (Hsc'&?); eauto; subst Γ0.
             - instantiate (1:=fun '(blks, _) => flat_map idcaus_of_locals blks). auto.
             - erewrite map_fst_replace_idcaus, map_map, map_ext; eauto. intros; destruct_conjs; auto.
             - eapply wc_scope_incl; [| |eauto|].
               + intros * Has. eapply H18 in Has as (Has&?).
                 inv Has. econstructor; solve_In. destruct (assoc_ident _ _); auto.
               + intros * His. eapply H19 in His.
                 inv His. econstructor; solve_In. destruct (assoc_ident _ _); auto.
               + intros; simpl in *.
                 destruct_conjs; split; eauto; simpl_Forall; eauto using wc_block_incl, wc_exp_incl.
             - intros. eauto.
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
                 - intros * Hin' Hdep. eapply H46; eauto. solve_Exists.
                 - intros * Hin' Hdep. eapply H47; eauto.
                   2:solve_Exists. solve_In.
                 - split; eauto.
                   intros * Hdef' Hin' Hca. take (forall (y : ident), In _ _ -> _) and eapply it; eauto.
                   eapply VarsDefined_det in Hdef; eauto. now rewrite <-Hdef.
               } clear H.
               split.
               + intros * Hinxs Hca. inv_VarsDefined.
                 take (Permutation _ xs0) and rewrite <-it in Hinxs. apply in_concat in Hinxs as (?&?&?); inv_VarsDefined; simpl_Forall.
                 take (forall (x : ident) (xs : list ident), _ -> _) and eapply it; eauto.
               + simpl_Forall; eauto.
           } } clear H H27.
        split.
        + intros * Hinxs Hca1.
          assert (Syn.Is_defined_in y (Bauto Weak ck (ini0, oth) states)) as Hdef.
          { eapply VarsDefined_Is_defined; eauto. econstructor; eauto.
            eapply NoDupLocals_incl; [|econstructor; eauto]. auto. }
          assert (Is_defined_in Γ cy (Bauto Weak ck (ini0, oth) states)) as Hdef' by (eauto using Is_defined_in_Is_defined_in).
          eapply sc_var_inv_unselect with (tn:=List.length states) (sc:=stres) (Γ':=map (fun '(x, e) => (x, ann_with_clock e Cbase)) Γ); eauto.
          1:{ destruct states; try congruence. simpl; lia. }
          1:{ take (sem_transitions _ _ _ _ _ _) and eapply sem_automaton_wt_state1 in it; eauto. 1,3,4:simpl_Forall; auto.
              - repeat inv_branch. repeat inv_scope. simpl_Forall; auto.
              - repeat inv_branch. repeat inv_scope. intros k. specialize (Hf k). destruct_conjs. simpl_Forall.
                repeat inv_branch. repeat inv_scope. eauto.
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
                simpl_Forall. repeat inv_branch.
                destruct s. take (wc_scope _ _ _ _) and eapply wc_scope_Is_defined_in in it; eauto.
                2:{ intros; simpl in *; simpl_Exists; simpl_Forall.
                    eapply wc_block_Is_defined_in; eauto. }
                eapply InMembers_In in it as (?&Hin').
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
              repeat inv_branch. destruct s. take (VarsDefinedScope _ _ _) and eapply sem_scope_defined2 with (Hi:=(_,_)) in it; eauto.
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
        assert (Forall (fun '((e, _), br) => forall k, exists Hi',
                            Sem.select_hist e k stres1 Hi Hi'
                            /\ (forall y, In y xs -> HasCaus (map (fun '(x, e) => (x, ann_with_clock e Cbase)) Γ) y cy ->
                                    sc_var_inv (map (fun '(x, e) => (x, ann_with_clock e Cbase)) Γ) Hi' (fselectb e k stres1 bs) cy)
                            /\ sem_branch_ck'
                                (fun Γ s => sem_scope_ck'
                                           (fun Γ Hi blks => Forall (sem_block_ck' (cy::envP) Γ Hi (fselectb e k stres1 bs)) (fst blks))
                                           (cy :: envP) Γ Hi' (fselectb e k stres1 bs) (snd s))
                                (cy :: envP) (map (fun '(x, a) => (x, ann_with_clock a Cbase)) Γ) Hi' (fselectb e k stres1 bs) br)
                       states) as Hf.
        { simpl_Forall. intros. specialize (H25 k); destruct_conjs. destruct b as [?(?&[?(?&?)])]; destruct_conjs.
          do 2 esplit; eauto.
          take (wt_branch _ _) and eapply sc_branch
            with (P_dep:=fun Γ cx cy blks => depends_on_scope (fun Γ cx cy blks => Exists (depends_on Γ cx cy) (fst blks)) Γ cx cy (snd blks))
                 (Γ:=map (fun '(x, e) => (x, ann_with_clock e Cbase)) Γ) in it as (Hsc'&?); eauto.
          - clear - H0 Hnd1.
            eapply NoDup_locals_inv2; eauto.
            unfold idcaus_of_senv in *. erewrite map_map, map_filter_map, map_ext with (l:=Γ), map_filter_ext with (xs:=Γ); eauto.
            1,2:intros; destruct_conjs; auto.
          - apply NoDupMembers_map; auto.
          - erewrite map_map, map_ext; eauto. intros; destruct_conjs; auto.
          - apply Forall_forall; intros ? Hin. simpl_In. constructor.
          - take (Sem.select_hist _ _ _ _ _) and destruct it as (Href&_). eapply FEnv.dom_ub_refines; eauto.
            erewrite map_map, map_ext; eauto. intros; destruct_conjs; auto.
          - take (Sem.select_hist _ _ _ _ _) and destruct it as (_&Href). eapply FEnv.dom_ub_refines; eauto.
            erewrite map_map, map_ext; eauto. intros; destruct_conjs; auto.
          - intros * ? Hdep.
            split; intros ??? Hca Hck Hv; inv Hca; inv Hck; simpl_In.
            + destruct H1 as (Hselect&_). eapply sem_var_select_inv in Hv as (?&Hv&Hselect'); eauto.
              apply select_fselect in Hselect' as Heq. rewrite Heq in *. rewrite ac_fselect.
              constructor.
              assert (depends_on Γ cy (causl a0) (Bauto Strong ck ([], oth) states)) as Hdep2.
              { eapply depends_on_incl. 3:econstructor; solve_Exists; inv Hdep; [eapply DepOnBranch1|eapply DepOnBranch2]; eauto.
                1,2:intros * Has; inv Has; simpl_In; eauto with senv. }
              eapply fselectb_both_slower.
              * take (sem_clock _ _ _ bs') and eapply sc_slower in it.
                2:rewrite Hac1, <-stres_st_ac; eauto using depends_on_def_last, ac_aligned.
                eapply slower_ac_morph; [|eauto]. apply stres_st_ac.
              * apply ac_select in Hselect'. rewrite <-Hselect'.
                eauto using aligned_slower, ac_aligned.
            + destruct H1 as (_&Hselect). eapply sem_var_select_inv in Hv as (?&Hv&Hselect'); eauto.
              apply select_fselect in Hselect' as Heq. rewrite Heq in *. rewrite ac_fselect.
              constructor.
              assert (depends_on Γ cy cx (Bauto Strong ck ([], oth) states)) as Hdep2.
              { eapply depends_on_incl. 3:econstructor; solve_Exists; inv Hdep; [eapply DepOnBranch1|eapply DepOnBranch2]; eauto.
                1,2:intros * Has; inv Has; simpl_In; eauto with senv. }
              eapply fselectb_both_slower.
              * take (sem_clock _ _ _ bs') and eapply sc_slower in it.
                2:rewrite Hac1, <-stres_st_ac; eauto using depends_on_def_last, ac_aligned.
                eapply slower_ac_morph; [|eauto]. apply stres_st_ac.
              * apply ac_select in Hselect'. rewrite <-Hselect'.
                eauto using aligned_slower, ac_aligned.
          - intros ? Hin' Hdep. apply HenvP. solve_In.
            eapply depends_on_incl. 3:econstructor; solve_Exists; inv Hdep; [eapply DepOnBranch1|eapply DepOnBranch2]; eauto.
            1,2:intros * Has; inv Has; simpl_In; eauto with senv.
          -{ intros; simpl in *. destruct_conjs.
             take (wt_scope _ _ _ _) and eapply sc_scope
               with (P_dep:=fun Γ cx cy blks => Exists (depends_on Γ cx cy) (fst blks))
                    (Γ:=Γ0) in it as (Hsc'&?); eauto; subst Γ0.
             - instantiate (1:=fun '(blks, _) => flat_map idcaus_of_locals blks). auto.
             - erewrite map_fst_replace_idcaus, map_map, map_ext; eauto. intros; destruct_conjs; auto.
             - eapply wc_scope_incl; [| |eauto|].
               + intros * Has. eapply H17 in Has as (Has&?).
                 inv Has. econstructor; solve_In. destruct (assoc_ident _ _); auto.
               + intros * His. eapply H18 in His.
                 inv His. econstructor; solve_In. destruct (assoc_ident _ _); auto.
               + intros; simpl in *.
                 destruct_conjs; split; eauto; simpl_Forall; eauto using wc_block_incl, wc_exp_incl.
             - intros. eauto.
             - intros; simpl in *. destruct_conjs.
               assert (Forall (fun blks => (forall y xs, VarsDefined blks xs -> In y xs -> HasCaus Γ0 y cy ->
                                                 sc_var_inv Γ0 Hi0 (fselectb e k stres1 bs) cy)
                                        /\ sem_block_ck' (cy::envP) Γ0 Hi0 (fselectb e k stres1 bs) blks) l2) as Hf.
               { simpl_Forall. inv_VarsDefined.
                 edestruct H with (Γ:=Γ0) (xs:=xs1). 10:eauto. all:eauto.
                 - eapply NoDup_locals_inv; eauto.
                 - etransitivity; eauto using incl_concat.
                   take (Permutation _ _) and now rewrite it.
                 - intros * Hin' Hdep. eapply H44; eauto. solve_Exists.
                 - intros * Hin' Hdep. eapply H45; eauto.
                   2:solve_Exists. solve_In.
                 - split; eauto.
                   intros * Hdef' Hin' Hca. take (forall (y : ident), In _ _ -> _) and eapply it; eauto.
                   eapply VarsDefined_det in Hdef; eauto. now rewrite <-Hdef.
               } clear H.
               split.
               + intros * Hinxs Hca. inv_VarsDefined.
                 take (Permutation _ xs0) and rewrite <-it in Hinxs. apply in_concat in Hinxs as (?&?&?); inv_VarsDefined; simpl_Forall.
                 take (forall (x : ident) (xs : list ident), _ -> _) and eapply it; eauto.
               + simpl_Forall; eauto.
           } } clear H H25.
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
              - repeat inv_branch. repeat inv_scope. simpl_Forall; auto.
              - repeat inv_branch. intros. specialize (H24 k); destruct_conjs. repeat inv_branch. eauto. }
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
                repeat inv_branch. destruct s. take (wc_scope _ _ _ _) and eapply wc_scope_Is_defined_in in it; eauto.
                2:{ intros; simpl in *; simpl_Exists; simpl_Forall.
                    eapply wc_block_Is_defined_in; eauto. }
                eapply InMembers_In in it as (?&Hin').
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
              repeat inv_branch. destruct s. take (VarsDefinedScope _ _ _) and eapply sem_scope_defined2 with (Hi:=(_,_)) in it; eauto.
              take (sem_scope_ck' _ _ _ _ _ _) and inv it; econstructor; eauto; simpl_Forall; eauto using sem_block_ck'_sem_block.
          }
          eapply H0; eauto. inv Hca1; econstructor; solve_In. auto.
        + econstructor; eauto. simpl_Forall.
          specialize (Hf k); destruct_conjs; eauto.

      - (* locals *)
        eapply sc_scope in H8 as (?&?); eauto with lcaus.
        + split; eauto. constructor; eauto.
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
        + intros ? [? Hil]. inv Hil.
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
      - (* extcall *)
        destruct_conjs; simpl_Exists; simpl_Forall; eauto.
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
      - apply sc_exp_extcall; auto.
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
      1-6,11-12:(eapply Forall2_impl_In; [|eauto]; intros;
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

    Fact idcaus_of_senv_when_NoDup : forall ck Γ,
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

    Lemma sem_scope_sem_scope_ck {A} f_idcaus P_nd P_wt P_wc P_blk1 (P_blk2: _ -> _ -> Prop) :
      forall envP locs (blk: A) Γty Γck Γ' H bs,
        NoDupMembers Γty ->
        NoDupMembers Γck ->
        NoDup (map snd (idcaus_of_senv Γck ++ idcaus_of_scope f_idcaus (Scope locs blk))) ->
        NoDupScope P_nd (map fst Γty) (Scope locs blk) ->
        (forall x ty, HasType Γck x ty -> HasType Γty x ty) ->
        incl (map snd (idcaus_of_senv Γck ++ idcaus_of_scope f_idcaus (Scope locs blk))) envP ->
        FEnv.dom_ub (fst H) (map fst Γty) ->
        FEnv.dom_ub (snd H) (map fst Γty) ->
        sc_vars Γck H bs ->
        wt_scope P_wt G Γty (Scope locs blk) ->
        wc_env (idck Γck) ->
        Forall (fun '(_, a) => wc_clock (idck Γck) (clo a)) Γ' ->
        wc_scope P_wc G Γck (Scope locs blk) ->
        sem_scope_ck' G P_blk1 envP Γ' H bs (Scope locs blk) ->
        (forall Γty Γck Γ' Hi,
            NoDupMembers Γty ->
            NoDupMembers Γck ->
            NoDup (map snd (idcaus_of_senv Γck ++ f_idcaus blk)) ->
            P_nd (map fst Γty) blk ->
            (forall x ty, HasType Γck x ty -> HasType Γty x ty) ->
            incl (map snd (idcaus_of_senv Γck ++ f_idcaus blk)) envP ->
            FEnv.dom_ub (fst Hi) (map fst Γty) ->
            FEnv.dom_ub (snd Hi) (map fst Γty) ->
            sc_vars Γck Hi bs ->
            P_wt Γty blk ->
            wc_env (idck Γck) ->
            Forall (fun '(_, a) => wc_clock (idck Γck) (clo a)) Γ' ->
            P_wc Γck blk ->
            P_blk1 Γ' Hi blk ->
            P_blk2 Hi blk) ->
        sem_scope_ck (fun Hi => sem_exp_ck G Hi bs) P_blk2 H bs (Scope locs blk).
    Proof.
      intros * Hnd1 Hnd2 Hnd3 Hnd4 Hincl1 HenvP Hdom Hdoml Hsc Hwt Hwenv Hwenv' Hwc Hsem Hind;
        inv Hnd4; inv Hwt; inv Hwc; inv Hsem.
      assert (incl (map fst Γck) (map fst Γty)) as Hincl1'.
      { intros ? Hin. simpl_In. assert (HasType Γck a a0.(typ)) as Hty by eauto with senv.
        apply Hincl1 in Hty. inv Hty. solve_In. }
      assert (Hi ⊑ Hi + Hi') as Href1 by eauto using local_hist_dom_ub_refines.
      assert (Hl ⊑ Hl + Hl') as Href2 by eauto using local_hist_dom_ub_refines_last.
      assert (NoDupMembers (Γck ++ senv_of_locs locs)) as Hnd2'.
      { apply NoDupMembers_app; auto.
        - now apply NoDupMembers_senv_of_locs.
        - intros * Hinm1 Hinm2. rewrite InMembers_senv_of_locs in Hinm2.
          take (forall x, InMembers x locs -> ~_) and eapply it; eauto. apply Hincl1', fst_InMembers; auto.
      }

      assert (sc_vars (senv_of_locs locs) (Hi + Hi', Hl + Hl') bs) as Hsc1.
      { eapply sc_var_inv_sc_vars.
        - apply NoDupMembers_senv_of_locs; auto.
        - simpl_Forall.
          assert (In i0 envP) as HinP.
          { eapply HenvP.
            rewrite 2 map_app, 2 in_app_iff. right; left. solve_In. }
          simpl_Forall. eauto.
      }
      assert (sc_vars (Γck ++ senv_of_locs locs) (Hi + Hi', Hl + Hl') bs) as Hsc2.
      { apply local_hist_sc_vars with (Γ:=Γty); auto. }

      eapply Sscope; eauto.
      - intros. edestruct H14; destruct_conjs; eauto.
        do 3 esplit. repeat split; eauto using sem_var_refines. simpl_Forall.
        eapply sem_exp_sem_exp_ck with (Γ:=Γck ++ _); eauto.
        clear - Hnd3. rewrite idcaus_of_senv_app. solve_NoDup_app.
      - eapply Hind with (Γ':=Γ'++senv_of_locs locs) (Γty:=Γty++_); eauto.
        + apply NoDupMembers_app; auto.
          * apply NoDupMembers_senv_of_locs; auto.
          * intros * Hinm1 Hinm2. rewrite InMembers_senv_of_locs in Hinm2.
            eapply H5; eauto. apply fst_InMembers; auto.
        + clear - Hnd3. simpl in *.
          rewrite idcaus_of_senv_app.
          simpl_app. auto.
        + rewrite map_app, map_fst_senv_of_locs; auto.
        + intros *. rewrite 2 HasType_app. intros [|]; auto.
        + etransitivity; [|eauto].
          rewrite idcaus_of_senv_app. simpl_app. solve_incl_app.
        + rewrite map_app, map_fst_senv_of_locs.
          eapply local_hist_dom_ub; eauto.
        + rewrite map_app, map_fst_senv_of_locs.
          eapply local_hist_dom_ub_last; eauto.
        + simpl_app. eapply Forall_app; split; eauto.
          * eapply Forall_impl; [|eauto]; intros; simpl in *.
            eapply wc_clock_incl; [|eauto]. solve_incl_app.
          * simpl_Forall; eauto.
        + apply Forall_app; split; simpl_Forall; simpl_In; simpl_Forall; eauto.
          eapply wc_clock_incl; [|eauto]. solve_incl_app.
    Qed.

    Lemma sem_branch_sem_branch_ck {A} f_idcaus P_nd P_wt P_wc P_blk1 (P_blk2: _ -> Prop) :
      forall envP caus (blk: A) Γty Γck Γ' H bs,
        NoDupMembers Γty ->
        NoDupMembers Γck ->
        NoDup (map snd (idcaus_of_senv Γck ++ idcaus_of_branch f_idcaus (Branch caus blk))) ->
        NoDupBranch P_nd (Branch caus blk) ->
        (forall x ty, HasType Γck x ty -> HasType Γty x ty) ->
        incl (map snd (idcaus_of_senv Γck ++ idcaus_of_branch f_idcaus (Branch caus blk))) envP ->
        FEnv.dom_ub (fst H) (map fst Γty) ->
        sc_vars Γck H bs ->
        wt_branch P_wt (Branch caus blk) ->
        wc_env (idck Γck) ->
        Forall (fun '(_, a) => wc_clock (idck Γck) (clo a)) Γ' ->
        wc_branch P_wc (Branch caus blk) ->
        sem_branch_ck' P_blk1 envP Γ' H bs (Branch caus blk) ->
        (forall Γ',
            NoDup (map snd (idcaus_of_senv Γck ++ f_idcaus blk)) ->
            P_nd blk ->
            (forall x ty, HasType Γck x ty -> HasType Γty x ty) ->
            incl (map snd (idcaus_of_senv Γck ++ f_idcaus blk)) envP ->
            sc_vars Γck H bs ->
            P_wt blk ->
            wc_env (idck Γck) ->
            Forall (fun '(_, a) => wc_clock (idck Γck) (clo a)) Γ' ->
            P_wc blk ->
            P_blk1 Γ' blk ->
            P_blk2 blk) ->
        sem_branch P_blk2 (Branch caus blk).
    Proof.
      intros * Hnd1 Hnd2 Hnd3 Hnd4 Hincl1 HenvP Hdom Hsc Hwt Hwenv Hwenv' Hwc Hsem Hind;
        inv Hnd4; inv Hwt; inv Hwc; inv Hsem.
      constructor.
      eapply Hind with (Γ':=replace_idcaus caus Γ'); eauto.
      - simpl in *. solve_NoDup_app.
      - simpl in *. etransitivity; [|eauto].
        solve_incl_app.
      - simpl_Forall. simpl_In. simpl_Forall.
        destruct (assoc_ident _ _); auto.
    Qed.

    Local Ltac simpl_ndup Hnd :=
      simpl in *;
      try rewrite app_nil_r in Hnd; repeat rewrite map_app.

    Fact map_filter_HasClock : forall Γ Γ' ck,
        (forall x ck', HasClock Γ' x ck' -> HasClock Γ x ck /\ ck' = Cbase) ->
        forall x ck',
          HasClock Γ' x ck' ->
          HasClock (map_filter (fun '(x0, e0) => if clo e0 ==b ck then Some (x0, ann_with_clock e0 Cbase) else None) Γ) x ck'.
    Proof.
      intros * Hclocks * Hck.
      eapply Hclocks in Hck as (Hck&?); subst.
      inv Hck. econstructor. solve_In; simpl. rewrite equiv_decb_refl. eauto.
      auto.
    Qed.

    Fact map_filter_IsLast : forall Γ Γ' ck,
        NoDupMembers Γ ->
        (forall x ck', HasClock Γ' x ck' -> HasClock Γ x ck /\ ck' = Cbase) ->
        (forall x, IsLast Γ' x -> IsLast Γ x) ->
        forall x,
          IsLast Γ' x ->
          IsLast (map_filter (fun '(x0, e0) => if clo e0 ==b ck then Some (x0, ann_with_clock e0 Cbase) else None) Γ) x.
    Proof.
      intros * Hnd Hclocks Hlasts * Hl.
      specialize (Hlasts _ Hl). inv Hlasts. inv Hl.
      edestruct Hclocks as (Hck&?); eauto with senv. inv Hck.
      econstructor. solve_In; simpl. rewrite equiv_decb_refl. eauto.
      eapply NoDupMembers_det in H; eauto; subst.
      unfold ann_with_clock; simpl. auto.
    Qed.

    Lemma sem_block_sem_block_ck : forall envP blk Γty Γck Γ' H bs,
        NoDupMembers Γty ->
        NoDupMembers Γck ->
        NoDup (map snd (idcaus_of_senv Γck ++ idcaus_of_locals blk)) ->
        NoDupLocals (map fst Γty) blk ->
        (forall x ty, HasType Γck x ty -> HasType Γty x ty) ->
        incl (map snd (idcaus_of_senv Γck ++ idcaus_of_locals blk)) envP ->
        FEnv.dom_ub (fst H) (map fst Γty) ->
        FEnv.dom_ub (snd H) (map fst Γty) ->
        sc_vars Γck H bs ->
        wt_block G Γty blk ->
        wc_env (idck Γck) ->
        Forall (fun '(_, a) => wc_clock (idck Γck) (clo a)) Γ' ->
        wc_block G Γck blk ->
        sem_block_ck' G envP Γ' H bs blk ->
        sem_block_ck G H bs blk.
    Proof.
      induction blk using block_ind2;
        intros * Hnd1 Hnd2 Hnd5 Hnd6 Hincl1 HenvP Hdom Hdoml Hsc Hwt Hwenv Hwenv' Hwc Hsem;
        inv Hnd6; inv Hwt; inv Hwc; inv Hsem; simpl_ndup Hnd1.

      - (* equation *)
        constructor. eapply sem_equation_sem_equation_ck with (Γ:=Γck); eauto.
        rewrite app_nil_r in Hnd5; auto.

      - (* reset *)
        econstructor; eauto.
        + take (sem_exp _ _ _ _ _) and assert (Hsem2:=it).
          eapply sem_exp_sem_exp_ck with (Γ:=Γck) in Hsem2; eauto.
          rewrite map_app in Hnd5; eauto using NoDup_app_l.
        + intros k. specialize (H15 k). simpl_Forall. inv_VarsDefined.
          eapply H with (Γty:=Γty); eauto.
          * eapply NoDup_locals_inv; eauto.
          (* * etransitivity; eauto using incl_concat. *)
          * etransitivity; [|eauto]. rewrite 2 map_app. apply incl_appr'.
            intros ??. solve_In.
          * eapply FEnv.dom_ub_map; eauto.
          * eapply FEnv.dom_ub_map; eauto.
          * eapply sc_vars_mask; eauto.

      - (* switch *)
        assert (sem_clock (fst H0) bs ck (abstract_clock sc)) as Hsemck.
        { eapply sc_exp'' with (Γ:=Γck) in H14; eauto.
          take (clockof _ = _) and rewrite it in H14; simpl_Forall; eauto.
        }
        assert (incl (map fst Γck) (map fst Γty)) as Hincl'.
        { intros ? Hv. simpl_In. assert (HasType Γck a a0.(typ)) as Hty by eauto with senv.
          specialize (Hincl1 _ _ Hty). inv Hincl1. do 2 esplit; eauto. auto. }

        econstructor; eauto.
        + eapply sem_exp_sem_exp_ck with (Γ:=Γck) in H14; eauto.
          solve_NoDup_app.
        + simpl_Forall.
          do 2 esplit; eauto.
          destruct b. eapply sem_branch_sem_branch_ck
            with (Γty:=Γty)
                 (Γck:=map_filter (fun '(x, e) => if e.(clo) ==b ck then Some (x, ann_with_clock e Cbase) else None) Γck)
                 (Γ':=map (fun '(x, a) => (x, ann_with_clock a Cbase)) Γ'); eauto.
          * eapply NoDupMembers_map_filter; eauto.
            intros *. destruct (_ ==b _); simpl; auto.
          * subst. eapply NoDup_locals_inv2; eauto.
            rewrite map_app in *. eapply NoDup_incl_app2. 3:apply Hnd5.
            -- intros ? Hin. unfold idcaus_of_senv in *. rewrite map_app, in_app_iff in *.
               destruct Hin; [left|right]; simpl_In; destruct (_ ==b _) eqn:Heq; inv Hf; rewrite equiv_decb_equiv in Heq; inv Heq; simpl in *.
               1,2:solve_In; try rewrite Hf0; simpl; eauto. auto.
            -- intros Hnd. eapply idcaus_of_senv_when_NoDup; eauto.
          * subst. intros * Hty. apply Hincl1.
            inv Hty. simpl_In.
            destruct (_ ==b _) eqn:Heq; inv Hf; rewrite equiv_decb_equiv in Heq. eauto with senv.
          * subst. etransitivity; [|eapply HenvP].
            rewrite 2 map_app. apply incl_app; [apply incl_appl|apply incl_appr; intros ??; solve_In].
            unfold idcaus_of_senv. simpl_app. repeat rewrite map_map.
            apply incl_app; [apply incl_appl|apply incl_appr].
            1-2:intros ??; solve_In. 1,3:destruct (_ ==b _); inv Hf; eauto; simpl in *. rewrite Hf0; simpl; eauto. auto.
          * destruct H0. eapply FEnv.dom_ub_refines; eauto.
          * eapply sc_vars_when; eauto.
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
         *{ intros; simpl in *; simpl_Forall. inv_VarsDefined.
            eapply H with (Γty:=Γty) (Γck:=map_filter _ Γck); eauto using NoDup_locals_inv.
            - apply NoDupMembers_map_filter; auto. intros; cases; simpl; auto.
            - etransitivity; eauto. rewrite 2 map_app. apply incl_appr'. intros ??; solve_In.
            - destruct H0. eapply FEnv.dom_ub_refines; eauto.
            - destruct H0. eapply FEnv.dom_ub_refines; eauto.
            - eapply wc_block_incl. 3:eauto. 1,2:eauto using map_filter_HasClock, map_filter_IsLast.
          }


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
          - apply NoDupMembers_map_filter; auto.
            intros; destruct (_ ==b _); simpl; auto.
          - split; auto.
            eapply wc_exp_incl; [| |eauto]; eauto using map_filter_HasClock, map_filter_IsLast.
        }
        assert (incl (map fst Γck) (map fst Γty)) as Hincl'.
        { intros ? Hv. simpl_In. assert (HasType Γck a a0.(typ)) as Hty by eauto with senv.
          specialize (Hincl1 _ _ Hty). inv Hincl1. do 2 esplit; eauto. auto. }

        econstructor; eauto.
        + eapply sem_transitions_sem_transitions_ck with (Γ:=map_filter (fun '(x, e) => if e.(clo) ==b ck then Some (x, ann_with_clock e Cbase) else None) Γck); eauto. 3,4:simpl_Forall; eauto.
          * apply NoDupMembers_map_filter; auto.
            intros; destruct (_ ==b _); simpl; auto.
          * rewrite map_app in Hnd5. apply idcaus_of_senv_when_NoDup; eauto using NoDup_app_l.
          * eapply wc_exp_incl; [| |eauto]; eauto using map_filter_HasClock, map_filter_IsLast.
        + simpl_Forall. take (forall k, _) and specialize (it k); destruct_conjs.
          do 2 esplit; eauto. destruct b as [?(?&[?(?&?)])].
          eapply sem_branch_sem_branch_ck
            with (Γty:=Γty) (H:=(t1, t2))
                 (Γck:=map_filter (fun '(x, e) => if e.(clo) ==b ck then Some (x, ann_with_clock e Cbase) else None) Γck)
                 (Γ':=map (fun '(x, a) => (x, ann_with_clock a Cbase)) Γ'); eauto.
         * eapply NoDupMembers_map_filter; eauto.
            intros *. destruct (_ ==b _); simpl; auto.
          * subst. eapply NoDup_locals_inv2; eauto.
            rewrite map_app in *. eapply NoDup_incl_app2. 3:apply Hnd5.
            -- intros ? Hin. unfold idcaus_of_senv in *. rewrite map_app, in_app_iff in *.
               destruct Hin; [left|right]; simpl_In; destruct (_ ==b _) eqn:Heq; inv Hf; rewrite equiv_decb_equiv in Heq; inv Heq; simpl in *.
               1,2:solve_In; try rewrite Hf0; simpl; eauto. auto.
            -- intros Hnd. eapply idcaus_of_senv_when_NoDup; eauto.
          * subst. intros * Hty. apply Hincl1.
            inv Hty. simpl_In.
            destruct (_ ==b _) eqn:Heq; inv Hf; rewrite equiv_decb_equiv in Heq. eauto with senv.
          * subst. etransitivity; [|eapply HenvP].
            rewrite 2 map_app. apply incl_app; [apply incl_appl|apply incl_appr; intros ??; solve_In].
            unfold idcaus_of_senv. simpl_app. repeat rewrite map_map.
            apply incl_app; [apply incl_appl|apply incl_appr].
            1-2:intros ??; solve_In. 1,3:destruct (_ ==b _); inv Hf; eauto; simpl in *. rewrite Hf0; simpl; eauto. auto.
          * destruct H0. eapply FEnv.dom_ub_refines; eauto.
          * take (sem_clock _ _ _ _) and rewrite Hac in it.
            eapply sc_vars_select; eauto.
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
          *{ intros; simpl in *; destruct_conjs; simpl_Forall. inv_VarsDefined.
             eapply sem_scope_sem_scope_ck
               with (Γty:=Γty)
                    (Γck:=map_filter (fun '(x, e) => if e.(clo) ==b ck then Some (x, ann_with_clock e Cbase) else None) Γck)
                    (Γ':=Γ'1); eauto.
             - apply NoDupMembers_map_filter; auto. intros; cases; simpl; auto.
             - instantiate (1:=fun '(blks, _) => flat_map idcaus_of_locals blks). eauto.
             - eauto.
             - destruct H0. eapply FEnv.dom_ub_refines; eauto.
             - destruct H0. eapply FEnv.dom_ub_refines; eauto.
             - eapply wc_scope_incl. 3:eauto.
               3:intros; destruct_conjs; split; simpl_Forall; eauto using wc_exp_incl, wc_block_incl.
               1,2:eauto using map_filter_HasClock, map_filter_IsLast.
             - intros; simpl in *; destruct_conjs; split.
               + simpl_Forall. inv_VarsDefined.
                 eapply H with (Γty:=Γty0); eauto using NoDup_locals_inv.
                 etransitivity; eauto. solve_incl_app. intros ??; solve_In.
               + eapply sem_transitions_sem_transitions_ck; eauto.
                 * solve_NoDup_app.
                 * simpl_Forall; eauto.
                 * simpl_Forall; eauto.
          }

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
        + simpl_Forall. specialize (H23 k); destruct_conjs.
          do 2 esplit; eauto.
          repeat (Syn.inv_branch || Clo.inv_branch || Typ.inv_branch || inv_branch).
          econstructor. eapply sem_transitions_sem_transitions_ck with (Γ:=map_filter (fun '(x, e) => if e.(clo) ==b ck then Some (x, ann_with_clock e Cbase) else None) Γck); eauto.
          * apply NoDupMembers_map_filter; auto.
            intros; destruct (_ ==b _); simpl; auto.
          * rewrite map_app in Hnd5. apply idcaus_of_senv_when_NoDup; eauto using NoDup_app_l.
          * take (sem_clock _ _ _ _) and rewrite Hac in it. eapply sc_vars_select; eauto.
            -- subst. intros * Hck. inv Hck; simpl_In.
               destruct (_ ==b _) eqn:Heq; inv Hf; rewrite equiv_decb_equiv in Heq; inv Heq.
               eauto with senv.
            -- subst. intros * Hca. inv Hca; simpl_In.
               destruct (_ ==b _) eqn:Heq; inv Hf; rewrite equiv_decb_equiv in Heq; inv Heq.
               eauto with senv.
          * simpl_Forall; eauto.
          * simpl_Forall. eapply wc_exp_incl. 3:eauto.
            1,2:eauto using map_filter_HasClock, map_filter_IsLast.
        + simpl_Forall. specialize (H24 k); destruct_conjs.
          do 2 esplit; eauto. destruct b as [?(?&[?(?&?)])].
          eapply sem_branch_sem_branch_ck
            with (Γty:=Γty) (H:=(t1, t2))
                 (Γck:=map_filter (fun '(x, e) => if e.(clo) ==b ck then Some (x, ann_with_clock e Cbase) else None) Γck)
                 (Γ':=map (fun '(x, a) => (x, ann_with_clock a Cbase)) Γ'); eauto.
         * eapply NoDupMembers_map_filter; eauto.
            intros *. destruct (_ ==b _); simpl; auto.
          * subst. eapply NoDup_locals_inv2; eauto.
            rewrite map_app in *. eapply NoDup_incl_app2. 3:apply Hnd5.
            -- intros ? Hin. unfold idcaus_of_senv in *. rewrite map_app, in_app_iff in *.
               destruct Hin; [left|right]; simpl_In; destruct (_ ==b _) eqn:Heq; inv Hf; rewrite equiv_decb_equiv in Heq; inv Heq; simpl in *.
               1,2:solve_In; try rewrite Hf0; simpl; eauto. auto.
            -- intros Hnd. eapply idcaus_of_senv_when_NoDup; eauto.
          * subst. intros * Hty. apply Hincl1.
            inv Hty. simpl_In.
            destruct (_ ==b _) eqn:Heq; inv Hf; rewrite equiv_decb_equiv in Heq. eauto with senv.
          * subst. etransitivity; [|eapply HenvP].
            rewrite 2 map_app. apply incl_app; [apply incl_appl|apply incl_appr; intros ??; solve_In].
            unfold idcaus_of_senv. simpl_app. repeat rewrite map_map.
            apply incl_app; [apply incl_appl|apply incl_appr].
            1-2:intros ??; solve_In. 1,3:destruct (_ ==b _); inv Hf; eauto; simpl in *. rewrite Hf0; simpl; eauto. auto.
          * destruct H1. eapply FEnv.dom_ub_refines; eauto.
          * take (sem_clock _ _ _ _) and rewrite Hac1 in it.
            eapply sc_vars_select; eauto.
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
          *{ intros; simpl in *; destruct_conjs; simpl_Forall. inv_VarsDefined.
             eapply sem_scope_sem_scope_ck
               with (Γty:=Γty)
                    (Γck:=map_filter (fun '(x, e) => if e.(clo) ==b ck then Some (x, ann_with_clock e Cbase) else None) Γck)
                    (Γ':=Γ'1); eauto.
             - apply NoDupMembers_map_filter; auto. intros; cases; simpl; auto.
             - instantiate (1:=fun '(blks, _) => flat_map idcaus_of_locals blks). eauto.
             - eauto.
             - destruct H1. eapply FEnv.dom_ub_refines; eauto.
             - destruct H1. eapply FEnv.dom_ub_refines; eauto.
             - eapply wc_scope_incl. 3:eauto.
               3:intros; destruct_conjs; split; simpl_Forall; eauto using wc_exp_incl, wc_block_incl.
               1,2:eauto using map_filter_HasClock, map_filter_IsLast.
             - intros; simpl in *.
               simpl_Forall. inv_VarsDefined.
               eapply H with (Γty:=Γty0); eauto using NoDup_locals_inv.
               etransitivity; eauto. solve_incl_app. intros ??; solve_In.
           }

      - (* locals *)
        constructor.
        eapply sem_scope_sem_scope_ck with (Γty:=Γty); eauto.
        + intros; simpl in *. simpl_Forall. inv_VarsDefined.
          eapply H with (Γty:=Γty0); eauto.
          * eapply NoDup_locals_inv; eauto.
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
    intros [] Hwt Hwc.
    assert (Ordered_nodes (Global types0 externs0 nodes0)) as Hord by (eauto using wl_global_Ordered_nodes with ltyping).
    revert Hwc Hord.
    induction nodes0; intros Hwc Hord Hcaus ??? Hsem Hckins. now inversion Hsem.
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
      assert (wc_global (Global types0 externs0 nodes0)) as Hvars by eauto.
      eapply sem_node_sc_vars in Hvars as (Hvars&Hloc); eauto.
      2:{ intros. eapply IHnodes0; eauto. inv Hwt. inv H7. constructor; auto. }
      2:{ inv Hwt; inv H5; destruct H8; auto. }
      2:{ eapply sc_var_inv_intro; eauto. }

      (* sem_node_ck *)
      pose proof (n_defd n) as (?&Hdef&Hperm).
      eapply sem_block_sem_block_ck in Hloc; eauto; auto with datatypes.
      eapply Snode with (H:=H'); autorewrite with list; eauto.
      + rewrite find_node_now; auto.
      + eapply sem_block_ck_cons'; eauto.
      + unfold clocked_node. split; auto.
        rewrite map_fst_senv_of_inout; auto.
      + intros. eapply IHnodes0; eauto. inv Hwt; inv H7; constructor; auto.
      + apply NoDupMembers_map, n_nodup. intros; destruct_conjs; auto.
      + rewrite fst_NoDupMembers, map_fst_senv_of_inout, <-fst_NoDupMembers. apply n_nodup.
      + simpl. destruct H2 as (Hnd&_). rewrite idcaus_of_senv_inout. auto.
      + rewrite map_fst_senv_of_inout. apply n_nodup.
      + simpl. rewrite idcaus_of_senv_inout. reflexivity.
      + rewrite map_fst_senv_of_inout; auto using FEnv.dom_dom_ub.
      + intros ? [? Hin]. inv Hin.
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
      inv Hord'. inv Hwt; inv H1. inv Hwc. inv Hcaus. eapply IHnodes0 in Hsem; eauto.
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
