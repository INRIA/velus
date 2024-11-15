From Coq Require Import BinPos List Permutation Morphisms.

From Velus Require Import Common Ident Environment Operators Clocks CoindStreams.
From Velus Require Import Lustre.StaticEnv Lustre.LSyntax Lustre.LOrdered Lustre.LSemantics Lustre.LTyping Lustre.LClocking Lustre.LCausality.

From Velus Require Import FunctionalEnvironment.
From Velus Require Import Lustre.Denot.Cpo.

Close Scope equiv_scope. (* conflicting notation "==" *)

Require Import CommonList2 CommonDS SDfuns SD Infty InftyProof CheckOp OpErr Safe Abs Lp ResetMask Restr.

Import List ListNotations.

Module Type SDTOREL
       (Import Ids   : IDS)
       (Import Op    : OPERATORS)
       (Import OpAux : OPERATORS_AUX Ids Op)
       (Import Cks   : CLOCKS        Ids Op OpAux)
       (Import Senv  : STATICENV     Ids Op OpAux Cks)
       (Import Syn   : LSYNTAX       Ids Op OpAux Cks Senv)
       (Import Typ   : LTYPING       Ids Op OpAux Cks Senv Syn)
       (Import Cl    : LCLOCKING     Ids Op OpAux Cks Senv Syn)
       (Import Caus  : LCAUSALITY    Ids Op OpAux Cks Senv Syn)
       (Import Lord  : LORDERED      Ids Op OpAux Cks Senv Syn)
       (Import Str   : COINDSTREAMS  Ids Op OpAux Cks)
       (Import Sem   : LSEMANTICS Ids Op OpAux Cks Senv Syn Lord Str)
       (Import Den   : SD         Ids Op OpAux Cks Senv Syn Lord)
       (Import Restr : LRESTR     Ids Op OpAux Cks Senv Syn)
       (Import Inf   : LDENOTINF  Ids Op OpAux Cks Senv Syn Typ Caus Lord Restr Den)
       (Import Ckop  : CHECKOP       Ids Op OpAux Cks Senv Syn)
       (Import OpErr : OP_ERR        Ids Op OpAux Cks Senv Syn Typ Restr Lord Den Ckop)
       (Import Safe  : LDENOTSAFE Ids Op OpAux Cks Senv Syn Typ Restr Cl Lord Den Ckop OpErr)
       (Import Abs   : ABS_INDEP  Ids Op OpAux Cks Senv Syn Typ Lord Den)
       (Import Lp    : LP         Ids Op OpAux Cks Senv Syn Typ Lord Den).


(* TODO: ajouter à Vélus *)
Global Instance : Symmetric history_equiv.
Proof.
  intros H1 H2 Eq v.
  destruct (Eq v); constructor.
  now symmetry.
Qed.

(* TODO: ajouter à Vélus *)
Global Instance eq_EqSts : forall A, subrelation (@eq (list (Stream A))) (@EqSts A).
Proof.
  intros ????; now subst.
Qed.

(* TODO: ajouter à Vélus  (iff vs Basics.impl *)
Global Add Parametric Morphism {PSyn Prefs} (G : @global PSyn Prefs) : (sem_exp G)
    with signature history_equiv ==> @EqSt bool ==> eq ==> @EqSts svalue ==> iff
      as sem_exp_iff.
Proof.
  intros ?? Eq1 ?? Eq2 ??? Eq3.
  split; rewrite Eq1, Eq2, Eq3; auto.
Qed.

(* TODO: ajouter à Vélus *)
Lemma sem_var_restrict :
  forall H Γ x s,
    IsVar Γ x ->
    sem_var H (Var x) s ->
    sem_var (restrict H Γ) (Var x) s.
Proof.
  clear.
  intros * Hv Hs.
  inv Hs.
  econstructor; eauto.
  apply FEnv.restrict_find; auto.
  apply vars_of_senv_Var; auto.
Qed.

(* TODO: ajouter à Vélus *)
Lemma vars_of_senv_app :
  forall Γ1 Γ2,
    vars_of_senv (Γ1 ++ Γ2) = vars_of_senv Γ1 ++ vars_of_senv Γ2.
Proof.
  unfold vars_of_senv.
  intros.
  now rewrite flat_map_app.
Qed.

(* TODO: ajouter à Vélus *)
Lemma union_restrict :
  forall Γ1 Γ2 H,
    history_equiv (restrict H Γ1 + restrict H Γ2) (restrict H (Γ1 ++ Γ2)).
Proof.
  clear.
  unfold history_equiv, FEnv.Equiv, restrict, FEnv.restrict, FEnv.union.
  intros; cases_eqn Hex.
  all: try constructor.
  all: try rewrite Hex; try constructor; try reflexivity.
  (* reste les contradictions *)
  all: exfalso; rewrite vars_of_senv_app, existsb_app in *.
  all: try take (_ || _ = true) and apply Bool.orb_prop in it as [].
  all: try take (_ || _ = false) and apply Bool.orb_false_elim in it as [].
  all: congruence.
Qed.

(* TODO: ajouter à Vélus *)
Lemma dom_restrict :
  forall H Γ,
    dom_lb H Γ ->
    dom (restrict H Γ) Γ.
Proof.
  clear.
  unfold dom, dom_lb.
  intros * [].
  setoid_rewrite FEnv.restrict_In.
  setoid_rewrite vars_of_senv_Var.
  setoid_rewrite vars_of_senv_Last.
  split; split; firstorder.
Qed.

Import RelationPairs.

(* TODO: remplacer celui de Vélus *)
Global Add Parametric Morphism : merge
       with signature @EqSt _ ==> Forall2 (eq * (@EqSt _)) ==> @EqSt _ ==> Basics.impl
         as merge_morph1.
Proof.
  cofix Cofix.
  intros cs cs' Ecs lxs lxs' Elxs os os' Eos Hc.
  destruct cs' as [[]], os' as [[]];
    inv Hc; inv Ecs; inv Eos; simpl in *;
    try discriminate.
  - constructor.
    + eapply Cofix; eauto.
      simpl_Forall.
      take ((eq * _)%signature _ _) and destruct it as [? HH].
      unfold RelCompFun in *; simpl in *; now rewrite HH.
    + simpl_Forall.
      eapply Forall2_in_right in Elxs as (?&?& [? HH]); eauto.
      unfold RelCompFun in *; simpl in *; rewrite <- HH.
      simpl_Forall; auto.
  - repeat take (_ = _) and inv it.
    constructor.
    + eapply Cofix; eauto.
      simpl_Forall.
      take ((eq * _)%signature _ _) and destruct it as [? HH].
      unfold RelCompFun in *; simpl in *; now rewrite HH.
    + take (Exists _ _) and apply Exists_exists in it as ([] &?&?&?); subst.
      eapply Forall2_in_left in Elxs as ([] &?& [? HH]); eauto.
      unfold RelCompFun in *; simpl in *; subst.
      solve_Exists; eauto; now rewrite <- HH.
    + simpl_Forall.
      eapply Forall2_in_right in Elxs as ([] &?& [? HH]); eauto.
      unfold RelCompFun in *; simpl in *; subst.
      simpl_Forall; now rewrite <- HH.
Qed.

(* TODO: remplacer celui de Vélus *)
Global Add Parametric Morphism : case
       with signature
       @EqSt _ ==> Forall2 (eq * (@EqSt _)) ==> orel (@EqSt _) ==> @EqSt _ ==> Basics.impl
         as case_morph1.
Proof.
  cofix Cofix.
  intros cs cs' Ecs lxs lxs' Elxs ds ds' Eds os os' Eos Hc.
  destruct cs' as [[]], os' as [[]];
    inv Hc; inv Ecs; inv Eos; simpl in *;
    try discriminate.
  - constructor.
    + eapply Cofix; eauto.
      * simpl_Forall.
        take ((eq * _)%signature _ _) and destruct it as [? HH].
        unfold RelCompFun in *; simpl in *; now rewrite HH.
      * inv Eds; constructor; eauto using tl_EqSt.
    + simpl_Forall.
      eapply Forall2_in_right in Elxs as (?&?& [? HH]); eauto.
      unfold RelCompFun in *; simpl in *; rewrite <- HH.
      simpl_Forall; auto.
    + inv Eds; simpl; auto; erewrite <- hd_EqSt; eauto.
  - repeat take (_ = _) and inv it.
    constructor.
    + eapply Cofix; eauto.
      * simpl_Forall.
        take ((eq * _)%signature _ _) and destruct it as [? HH].
        unfold RelCompFun in *; simpl in *; now rewrite HH.
      * inv Eds; constructor; eauto using tl_EqSt.
    + simpl_Forall.
      eapply Forall2_in_right in Elxs as (?&?& [? HH]); eauto.
      unfold RelCompFun in *; simpl in *; rewrite <- HH.
      simpl_Forall; auto.
    + inv Eds; simpl; auto; erewrite <- hd_EqSt; eauto.
    + take (Exists _ _) and apply Exists_exists in it as ([] &?&?&?); subst.
      eapply Forall2_in_left in Elxs as ([] &?& [? HH]); eauto.
      unfold RelCompFun in *; simpl in *; subst.
      solve_Exists; eauto; now rewrite <- HH.
  - repeat take (_ = _) and inv it.
    inv Eds.
    destruct sy; take (_ ⋅ _ ≡ _) and destruct it as [HHH Htl].
    simpl in *; inv HHH.
    apply CasePDef.
    + eapply Cofix; eauto.
      * simpl_Forall.
        take ((eq * _)%signature _ _) and destruct it as [? HH].
        unfold RelCompFun in *; simpl in *; now rewrite HH.
      * now constructor.
    + simpl_Forall.
      eapply Forall2_in_right in Elxs as (?&?& [? HH]); eauto.
      unfold RelCompFun in *; simpl in *; rewrite <- HH.
      simpl_Forall; auto.
    + simpl_Forall.
      eapply Forall2_in_right in Elxs as (?&?& [HH]); eauto.
      unfold RelCompFun in *; simpl in *; subst.
      simpl_Forall; auto.
Qed.


(* remember with [Streams.EqSts] instead of [eq] *)
Tactic Notation "remember_sts" constr(s) "as" ident(x) :=
  let Hx := fresh "H"x in
  remember s as x eqn:Hx;
  apply symmetry, eq_EqSts in Hx.


(** Dans cette section on donne une définition alternative aux règles
    du merge/case (LSemantics.Smerge/ScaseTotal/Scasedefault),
    qui ne manipule plus de Forall2Brs mais plutôt du Forall2t.
    Ça correspond mieux aux définitions de Denot.v, notamment [denot_expss]. *)
Section Sem_alt.

  (** Comment obtenir le prédicat Forall2Brs de LSemantics.Smerge sans
      avoir à manipuler de Forall3... *)
  Lemma Forall2Brs_transp :
    forall {PSyn Prefs} (G : @global PSyn Prefs),
    forall H b,
    forall ess vss d Hk,
      vss <> [] ->
      Forall2
        (fun '(t, es) (vs : list (enumtag * Stream svalue)) =>
           exists xss : list (list (Stream svalue)),
             Forall2 (sem_exp G H b) es xss /\ vs = map (pair t) (concat xss)) ess vss ->
      Forall2Brs (sem_exp G H b) ess (proj1_sig (transp d vss Hk)).
  Proof.
    intros * Nnil Hf.
    destruct (transp d vss Hk) as (vsst & HH & Hnm).
    destruct HH as [Hlt Hllt]; auto; simpl in *; clear HH.
    destruct Hk as (k & Hk); simpl in *; subst.
    clear Nnil.
    revert dependent vsst.
    induction Hf; intros.
    - constructor.
      simpl_Forall. destruct x; simpl in *; congruence.
    - destruct x as (t, es).
      destruct H0 as (xss & Hsem & ?); subst.
      inv Hk.
      econstructor; eauto.
      + eapply (IHHf (map (@tl _) vsst)).
        * simpl_Forall. now rewrite map_length.
        * intros; destruct (Nat.le_gt_cases (length vsst) m).
          2: erewrite map_nth', <- tl_nth, Hnm; auto.
          setoid_rewrite nth_overflow at 2.
          2: rewrite map_length; auto.
          rewrite nth_nil, nth_overflow; auto.
          destruct (nth_in_or_default n l' []) as [| ->]; simpl in *; try lia.
          simpl_Forall; lia.
        * simpl_Forall. rewrite tl_length; lia.
      + rewrite Forall3_map_2, Forall3_same_2_3.
        clear IHHf.
        rewrite map_length in *.
        apply Forall2_forall2; split; intros; subst; auto.
        rewrite nth_indep with (d' := []); try lia.
        assert (In (nth n vsst []) vsst) as Hin.
        { apply nth_In; congruence. }
        simpl_Forall.
        destruct (nth n vsst []) eqn:GG; simpl in *; try lia.
        f_equal.
        specialize (Hnm O n).
        rewrite GG in Hnm; simpl in Hnm; subst.
        erewrite map_nth'; eauto.
  Qed.

  (** Cette définition semble plus naturelle : vss correspond exactement
      à la matrice de concaténation de [sem_exp] sur ess, l'opérateur
      merge relationnel est appliqué sur les lignes de la matrice
      grâce à Forall2t. *)
  Lemma Smerge_alt :
    forall {PSyn Prefs} (G : @global PSyn Prefs),
    forall H b x tx ess lann os,
    forall d (xs : Stream svalue) (vss : list (list (enumtag * Stream svalue))),
      sem_var H (Var x) xs ->
      vss <> [] ->
      Forall (fun l => length l = length os) vss ->
      Forall2 (fun '(t,es) vs =>
                 exists xss, Forall2 (sem_exp G H b) es xss
                        /\ vs = map (pair t) (concat xss)) ess vss  ->
      Forall2t d (merge xs) vss os ->
      sem_exp G H b (Emerge (x, tx) ess lann) os.
  Proof.
    intros * Hx Nnil Hl Hf Ht.
    unshelve eapply Forall2t_Forall2 in Ht; auto.
    unshelve eapply Forall2Brs_transp in Hf; eauto.
    revert Ht Hf.
    destruct (transp d vss _) as (vsst & HH); intros; simpl in *.
    destruct HH as ([Hlt Hllt] & Hnm); auto.
    apply Smerge with xs vsst; auto.
  Qed.

  Lemma ScaseTotal_alt :
    forall {PSyn Prefs} (G : @global PSyn Prefs),
    forall H b e ess tys ck os,
    forall d (s : Stream svalue) (vss : list (list (enumtag * Stream svalue))),
      vss <> [] ->
      (* Basile est d'accord pour virer la dépendance sur tys dans ScaseTotal,
         donc cette hypothèse va disparaitre : *)
      length tys = length os ->
      sem_exp G H b e [s] ->
      Forall (fun l => length l = length os) vss ->
      Forall2 (fun '(t,es) vs =>
                 exists xss, Forall2 (sem_exp G H b) es xss
                        /\ vs = map (pair t) (concat xss)) ess vss  ->
      Forall2t d (fun l => case s l None) vss os ->
      sem_exp G H b (Ecase e ess None (tys, ck)) os.
  Proof.
    intros * He Nnil Hl Hl2 Hf Ht.
    unshelve eapply Forall2t_Forall2 in Ht; auto.
    unshelve eapply Forall2Brs_transp in Hf; eauto.
    revert Ht Hf.
    destruct (transp d vss _) as (vsst & HH); intros; simpl in *.
    destruct HH as ([Hlt Hllt] & Hnm); auto.
    apply ScaseTotal with s vsst; auto.
  Qed.

  (* Dans l'idéal il faudrait un Forall3t pour gérer aussi les flots
     de la branche par défaut. Pour l'instant on utilise simplement
     Forall2t en combinant les flots par défaut et ceux de sortie. *)
  Lemma ScaseDefault_alt :
    forall {PSyn Prefs} (G : @global PSyn Prefs),
    forall H b e ess eds tys ck,
    forall d (s : Stream svalue) (sds : list (list (Stream svalue))) (vss : list (list (enumtag * Stream svalue))) os,
      vss <> [] ->
      sem_exp G H b e [s] ->
      wt_streams [s] (typeof e) ->
      Forall2 (sem_exp G H b) eds sds ->
      length (concat sds) = length os ->
      Forall (fun l => length l = length os) vss ->
      Forall2 (fun '(t,es) vs =>
                 exists xss, Forall2 (sem_exp G H b) es xss
                        /\ vs = map (pair t) (concat xss)) ess vss  ->
      Forall2t d (fun l dos => case s l (Some (fst dos)) (snd dos)) (vss) (combine (concat sds) os) ->
      sem_exp G H b (Ecase e ess (Some eds) (tys, ck)) os.
  Proof.
    intros * Nnil He Hwt Heds Hld Hl Hf Ht.
    assert (Forall (fun l => length l = length (combine (concat sds) os)) vss).
    { rewrite combine_length', Hld; auto. }
    unshelve eapply Forall2t_Forall2 in Ht; auto.
    unshelve eapply Forall2Brs_transp in Hf; eauto.
    revert Hf Ht.
    destruct (transp _ vss _) as (vsst & HH); intros; simpl in *.
    destruct HH as ([Hlt Hllt] & Hnm); auto.
    apply ScaseDefault with s vsst sds; auto.
    apply Forall3_map_2, Forall3_combine2; auto.
    simpl_Forall; auto.
  Qed.

Lemma EqSts_concat_eq :
  forall (s : list (Stream svalue)) (ss : list (list (Stream svalue))),
    EqSts s (concat ss) ->
    exists ss', Forall2 EqSts ss' ss
           /\ s = concat ss'.
Proof.
  intros ??; revert s.
  induction ss; intros * Heq.
  - inv Heq; eauto.
  - apply Forall2_app_inv_r in Heq as (?&?&?& Happ &?); subst.
    apply IHss in Happ as (?&?&?); subst; eauto.
Qed.


Lemma Smerge_alt2 :
  forall {PSyn Prefs} (G : @global PSyn Prefs),
  forall H b x tx ess lann os,
  forall d (xs : Stream svalue) (vss : list (list (Stream svalue))),
    sem_var H (Var x) xs ->
    vss <> [] ->
    Forall (fun l => length l = length os) vss ->
    Forall2 (fun '(_,es) vs =>
               exists xss, EqSts vs (concat xss)
                      /\ Forall2 (sem_exp G H b) es xss) ess vss  ->
    Forall2t d (fun ss => merge xs (combine (map fst ess) ss)) vss os ->
    sem_exp G H b (Emerge (x, tx) ess lann) os.
Proof.
  clear.
  intros * Hx Nnil Hl Hf Ht.
  eapply Smerge_alt  with (d := (56, Streams.const absent)) (xs := xs);
    try assumption.
  4: eapply Forall2t_combine in Ht; eauto.
  - destruct vss, ess; simpl in *; try congruence; inv Hf.
  - apply Forall2_length in Hf.
    apply Forall_map, Forall2_combine', Forall2_map_1.
    setoid_rewrite map_length.
    apply Forall2_ignore1'; auto.
  - apply Forall2_map_2.
    apply Forall3_combine'2.
    apply Forall3_map_2.
    apply Forall3_same_1_2.
    simpl_Forall; eauto.
    edestruct EqSts_concat_eq as (?& Heq &?); eauto; subst.
    eexists; split; auto; now rewrite Heq.
Qed.
Lemma ScaseTotal_alt2 :
  forall {PSyn Prefs} (G : @global PSyn Prefs),
  forall H b e ess tys ck os,
  forall d (s : Stream svalue) (vss : list (list (Stream svalue))),
    sem_exp G H b e [s] ->
    vss <> [] ->
    length tys = length os ->
    Forall (fun l => length l = length os) vss ->
    Forall2 (fun '(_,es) vs =>
               exists xss, EqSts vs (concat xss)
                      /\ Forall2 (sem_exp G H b) es xss) ess vss  ->
    Forall2t d (fun ss => case s (combine (map fst ess) ss) None) vss os ->
    sem_exp G H b (Ecase e ess None (tys, ck)) os.
Proof.
  clear.
  intros * He Nnil Hl Hl2 Hf Ht.
  eapply ScaseTotal_alt  with (d := (56, Streams.const absent)) (s := s);
    try assumption.
  4: eapply Forall2t_combine with (P := fun ts => case s ts None) in Ht; eauto.
  - destruct vss, ess; simpl in *; try congruence; inv Hf.
  - apply Forall2_length in Hf.
    apply Forall_map, Forall2_combine', Forall2_map_1.
    setoid_rewrite map_length.
    apply Forall2_ignore1'; auto.
  - apply Forall2_map_2.
    apply Forall3_combine'2.
    apply Forall3_map_2.
    apply Forall3_same_1_2.
    simpl_Forall; eauto.
    edestruct EqSts_concat_eq as (?& Heq &?); eauto; subst.
    eexists; split; auto; now rewrite Heq.
Qed.

Lemma ScaseDefault_alt2 :
  forall {PSyn Prefs} (G : @global PSyn Prefs),
  forall H b e ess eds tys ck,
  forall d (s : Stream svalue) (sds : list (list (Stream svalue))) (vss : list (list (Stream svalue))) os,
    vss <> [] ->
    sem_exp G H b e [s] ->
    wt_streams [s] (typeof e) ->
    Forall2 (sem_exp G H b) eds sds ->
    length (concat sds) = length os ->
    Forall (fun l => length l = length os) vss ->
    Forall2 (fun '(_,es) vs =>
               exists xss, EqSts vs (concat xss)
                      /\ Forall2 (sem_exp G H b) es xss) ess vss  ->
    Forall2t d (fun ss dos => case s (combine (map fst ess) ss) (Some (fst dos)) (snd dos)) vss (combine (concat sds) os) ->
    sem_exp G H b (Ecase e ess (Some eds) (tys, ck)) os.
Proof.
  clear.
  intros * Nnil He Hwt Heds Hld Hl Hf Ht.
  eapply ScaseDefault_alt  with (d := (56, Streams.const absent)) (s := s) (sds := sds);
    try assumption.
  4: eapply Forall2t_combine with (P := fun ts => fun _ => case s ts _ _) in Ht; eauto.
  - destruct vss, ess; simpl in *; try congruence; inv Hf.
  - apply Forall2_length in Hf.
    apply Forall_map, Forall2_combine', Forall2_map_1.
    setoid_rewrite map_length.
    apply Forall2_ignore1'; auto.
  - apply Forall2_map_2.
    apply Forall3_combine'2.
    apply Forall3_map_2.
    apply Forall3_same_1_2.
    simpl_Forall; eauto.
    edestruct EqSts_concat_eq as (?& Heq &?); eauto; subst.
    eexists; split; auto; now rewrite Heq.
  - rewrite combine_length, Hld.
    simpl_Forall; lia.
Qed.


End Sem_alt.

(* piqué ailleurs *)
Section FromLClockedSemantics.
Lemma clocks_of_false :
  forall ss,
    clocks_of (List.map (fun _ : Stream svalue => Streams.const absent) ss) ≡ Streams.const false.
Proof.
  intros *.
  eapply ntheq_eqst. intros n.
  rewrite clocks_of_nth, const_nth.
  induction ss; simpl; auto.
  rewrite const_nth; simpl; auto.
Qed.
Lemma clocks_of_false2 :
  forall n,
    clocks_of (repeat (Streams.const absent) n) ≡ Streams.const false.
Proof.
  intros.
  eapply ntheq_eqst. intro k.
  rewrite clocks_of_nth, const_nth.
  induction n; simpl; auto.
  rewrite const_nth; simpl; auto.
Qed.
Lemma fby_absent {A}:
  @fby A (Streams.const absent) (Streams.const absent) (Streams.const absent).
Proof.
  cofix CoFix.
  rewrite CommonStreams.const_Cons. constructor; auto.
Qed.
(* à adapter de ClockedSem.sem_node_ck_cons' *)
Corollary sem_node_cons' :
  forall {PSyn Prefs} (nd : @node PSyn Prefs),
  forall nds types externs f xs ys,
      Ordered_nodes (Global types externs (nd::nds))
      -> sem_node (Global types externs nds) f xs ys
      -> nd.(n_name) <> f
      -> sem_node (Global types externs (nd::nds)) f xs ys.
Proof.
Admitted.

(* à adapter de ClockedSem.sem_block_ck_cons' *)
Lemma sem_block_cons' :
  forall {PSyn Prefs} (nd : @node PSyn Prefs),
  forall nds types externs bck Hi bk,
    Ordered_nodes (Global types externs (nd::nds))
    -> sem_block (Global types externs nds) Hi bk bck
    -> ~Is_node_in_block nd.(n_name) bck
    -> sem_block (Global types externs (nd::nds)) Hi bk bck.
Proof.
Admitted.
End FromLClockedSemantics.


(* TODO: à terme, mettre cette section dans LSemantics *)
Section Sem_absent.

Lemma wt_absent : forall ty, wt_stream (Streams.const absent) ty.
Proof.
  intro; cofix Cof.
  rewrite (unfold_Stream (Streams.const _)); constructor; cbn; auto.
Qed.

(* Hypothèse d'induction sur les nœuds du programme *)
Definition sem_global_abs {PSyn Prefs} (G : @global PSyn Prefs) :=
  forall f n,
    find_node f G = Some n ->
    let ss := repeat (Streams.const absent) (length (n_in n)) in
    let os := repeat (Streams.const absent) (length (n_out n)) in
    sem_node G f ss os.

Lemma sem_exp_absent :
  forall {PSyn Prefs} (G : @global PSyn Prefs),
  forall Γ,
    sem_global_abs G ->
    forall e,
    restr_exp e ->
    wt_exp G Γ e ->
    let H := fun _ => Some (Streams.const absent) in
    sem_exp G H (Streams.const false) e (repeat (Streams.const absent) (numstreams e)).
Proof.
  intros * HG.
  induction e using exp_ind2; intros Hr Hwt ?; inv Hr; inv Hwt.
  - (* Econst *)
    constructor.
    apply ntheq_eqst; intro.
    now rewrite const_nth', 2 const_nth.
  - (* Eenum *)
    constructor.
    apply ntheq_eqst; intro.
    now rewrite enum_nth', 2 const_nth.
  - (* Evar *)
    constructor; econstructor; now eauto.
  - (* Eunop *)
    take (typeof e = _) and rewrite <- length_typeof_numstreams, it in IHe.
    simpl in *; econstructor; eauto using Is_node_in_exp.
    eapply lift1_spec; intros.
    left. split; apply const_nth.
  - (* Ebinop *)
    take (typeof e1 = _) and rewrite <- length_typeof_numstreams, it in IHe1.
    take (typeof e2 = _) and rewrite <- length_typeof_numstreams, it in IHe2.
    simpl in *; econstructor; eauto using Is_node_in_exp.
    eapply lift2_spec; intros.
    left. repeat split; apply const_nth.
  - (* Efby *)
    apply Sfby with
      (s0ss := List.map (fun e => repeat (Streams.const absent) (numstreams e)) e0s)
      (sss := List.map (fun e => repeat (Streams.const absent) (numstreams e)) es); simpl.
    + clear H9 H10 H11.
      induction e0s; simpl in *; constructor; inv H; inv H4; inv H7; eauto.
    + clear H9 H10 H11.
      induction es; simpl in *; inv H0; inv H6; inv H8; constructor; auto.
    + rewrite <- 2 flat_map_concat_map, 2 flat_map_repeat.
      rewrite <- 2 annots_numstreams, <- 2 length_typesof_annots.
      take (typesof es = _) and rewrite it.
      take (typesof e0s = _) and rewrite it.
      rewrite map_length.
      apply Forall3_repeat, fby_absent.
  - (* Ewhen *)
    apply Swhen with
      (s := Streams.const absent)
      (ss := List.map (fun e => repeat (Streams.const absent) (numstreams e)) es); simpl.
    + rewrite Forall2_map_2. apply Forall2_same.
      apply Forall_impl_inside with (P := restr_exp) in H; auto.
      apply Forall_impl_inside with (P := wt_exp _ _) in H; auto.
    + econstructor; now eauto.
    + rewrite <- flat_map_concat_map, flat_map_repeat.
      rewrite <- annots_numstreams, <- length_typesof_annots.
      apply Forall2_repeat.
      apply when_spec. intros n.
      left. repeat split; apply const_nth.
  - (* Emerge *)
    simpl.
    pose (vss := map (fun '(t,es) => repeat (t, @Streams.const svalue absent)
                                    (list_sum (map numstreams es))) es).
    assert (Hl : Forall (fun l => length l = length tys) vss).
    { subst vss.
      simpl_Forall; subst.
      now rewrite repeat_length, length_typesof_annots, annots_numstreams. }
    eapply Smerge_alt with (d := (46, Streams.const absent)) (vss := vss);
      subst vss; rewrite ?repeat_length; auto using map_eq_nnil.
    + econstructor; now eauto.
    + subst H0.
      simpl_Forall.
      exists (map (fun e => repeat (Streams.const absent) (numstreams e)) l).
      split; simpl_Forall; eauto.
      rewrite concat_map, map_map, <- flat_map_repeat, flat_map_concat_map.
      f_equal; auto using map_ext, map_repeat.
    + eapply Forall2t_forall2 with (b := Streams.const absent);
        rewrite ?repeat_length; intros; auto.
      rewrite nth_repeat, map_map; simpl.
      apply merge_spec; intros.
      left; repeat split; auto using const_nth.
      simpl_Forall; subst.
      rewrite nth_repeat_in; simpl; auto using const_nth.
      now rewrite <- annots_numstreams, <- length_typesof_annots.
  - (* Ecase total *)
    simpl.
    take (typeof e = _) and rewrite <- length_typeof_numstreams, it in IHe.
    pose (vss := map (fun '(t,es) => repeat (t, @Streams.const svalue absent)
                                    (list_sum (map numstreams es))) es).
    assert (Hl : Forall (fun l => length l = length tys) vss).
    { subst vss.
      simpl_Forall; subst.
      now rewrite repeat_length, length_typesof_annots, annots_numstreams. }
    eapply ScaseTotal_alt
      with (d := (46, Streams.const absent)) (vss := vss) (s := Streams.const absent);
      subst vss; rewrite ?repeat_length; auto using map_eq_nnil.
    + subst H1.
      simpl_Forall.
      exists (map (fun e => repeat (Streams.const absent) (numstreams e)) l).
      split; simpl_Forall; eauto.
      rewrite concat_map, map_map, <- flat_map_repeat, flat_map_concat_map.
      f_equal; auto using map_ext, map_repeat.
    + eapply Forall2t_forall2 with (b := Streams.const absent);
        rewrite ?repeat_length; intros; auto.
      rewrite nth_repeat, map_map; simpl.
      apply case_spec; intros.
      left; repeat split; auto using const_nth.
      simpl_Forall; subst.
      rewrite nth_repeat_in; simpl; auto using const_nth.
      now rewrite <- annots_numstreams, <- length_typesof_annots.
  - (* Ecase défaut *)
    take (typeof e = _) and rewrite <- length_typeof_numstreams, it in IHe.
    pose (vss := map (fun '(t,es) => repeat (t, @Streams.const svalue absent)
                                    (list_sum (map numstreams es))) es).
    assert (Hl : (* utile dans la suite *)
     length (concat (map (fun e => repeat (@Streams.const svalue absent)
                                  (numstreams e)) des)) =
       length (repeat (@Streams.const svalue absent) (length (typesof des)))).
    { rewrite concat_length_sum, map_map, length_typesof_annots, annots_numstreams.
      now setoid_rewrite repeat_length. }
    eapply ScaseDefault_alt with
      (d := (46, Streams.const absent))
      (s := Streams.const absent)
      (sds := List.map (fun e => repeat (Streams.const absent) (numstreams e)) des)
      (vss := vss);
      subst vss; auto using map_eq_nnil.
    + (* wt_streams *)
      take (typeof e = _) and rewrite it.
      constructor; auto using wt_absent.
    + (* sds *)
      rewrite Forall2_map_2; apply Forall2_same.
      apply Forall_impl_inside with (P := restr_exp) in H0; auto.
      apply Forall_impl_inside with (P := wt_exp _ _) in H0; auto.
    + (* length *)
      simpl.
      simpl_Forall.
      rewrite 2 repeat_length.
      take (typesof _ = _) and rewrite <- it.
      now rewrite length_typesof_annots, annots_numstreams.
    + (* vss *)
      subst H1.
      simpl_Forall.
      exists (map (fun e => repeat (Streams.const absent) (numstreams e)) l).
      split; simpl_Forall; eauto.
      rewrite concat_map, map_map, <- flat_map_repeat, flat_map_concat_map.
      f_equal; auto using map_ext, map_repeat.
    + (* Forall2t *)
      eapply Forall2t_forall2; simpl.
      * simpl_Forall.
        rewrite combine_length'; auto.
        rewrite repeat_length in *.
        take (typesof _ = _) and rewrite <- it in *.
        rewrite <- annots_numstreams, <- length_typesof_annots; auto.
      * intros n Hn.
        rewrite <- flat_map_concat_map, flat_map_repeat.
        rewrite combine_nth, 2 nth_repeat; simpl.
        2: now rewrite 2 repeat_length, length_typesof_annots, annots_numstreams.
        apply case_spec; intros.
        left; repeat split; simpl; auto using const_nth.
        simpl_Forall; subst.
        rewrite nth_repeat_in; simpl; auto using const_nth.
        rewrite combine_length', concat_length_sum, map_map in Hn; auto.
        setoid_rewrite repeat_length in Hn.
        rewrite <- annots_numstreams, <- length_typesof_annots.
        take (typesof _ = _) and rewrite it.
        now rewrite length_typesof_annots, annots_numstreams.
  - (* Eapp *)
    apply Sapp with
      (ss := List.map (fun e => repeat (Streams.const absent) (numstreams e)) es)
      (rs := List.map (fun e => repeat (Streams.const absent) (numstreams e)) er)
      (bs := Streams.const false)
    ; simpl.
    + rewrite Forall2_map_2. apply Forall2_same.
      apply Forall_impl_inside with (P := restr_exp) in H; auto.
      apply Forall_impl_inside with (P := wt_exp _ _) in H; auto.
    + rewrite Forall2_map_2. apply Forall2_same.
      apply Forall_impl_inside with (P := restr_exp) in H0; auto.
      apply Forall_impl_inside with (P := wt_exp _ _) in H0; auto.
    + clear.
      rewrite <- flat_map_concat_map, flat_map_repeat, repeat_map.
      apply bools_ofs_absent.
    + intro k.
      rewrite <- flat_map_concat_map, flat_map_repeat, 2 map_repeat.
      rewrite <- annots_numstreams, <- length_typesof_annots.
      eapply sem_node_morph in HG; eauto.
      (* in *)
      take (Forall2 _ _ (n_in n)) and apply Forall2_length in it as ->.
      destruct k;
        [now setoid_rewrite mask_false_0 | now setoid_rewrite mask_false_S].
      (* out *)
      take (Forall2 _ _ (n_out n)) and apply Forall2_length in it.
      setoid_rewrite it.
      destruct k;
        [now setoid_rewrite mask_false_0 | now setoid_rewrite mask_false_S].
Qed.

(* construire une histroire absente sur [vars], None sinon *)
Definition abs_hist_of_vars (vars : list decl) : history :=
  fun x => match x with
        | Var x => if mem_ident x (List.map fst vars)
                  then Some (Streams.const absent)
                  else None
        | Last x => None
        end.

Lemma abs_hist_of_vars_dom :
  forall vars,
    Forall (fun '(_, (_, _, _, o)) => o = None) vars ->
    dom (abs_hist_of_vars vars) (senv_of_decls vars).
Proof.
  intro.
  unfold abs_hist_of_vars, senv_of_decls, dom, FEnv.In.
  split; intro x; (split; [intros (s & Hs)|intros Hf]); cases_eqn HH; eauto.
  - inv Hs.
    apply mem_ident_spec in HH.
    constructor.
    apply fst_InMembers; solve_In.
  - apply mem_ident_false in HH; contradict HH.
    inv Hf.
    apply fst_InMembers; solve_In.
  - congruence.
  - inv Hf.
    eapply in_map_iff in H0 as ((?&((?&?)&?)&?)&?&?).
    contradict H1.
    inv H0; simpl; auto.
    now simpl_Forall.
Qed.

(***************************************
 avec Ordered_nodes ça semble impossible car on ne peut pas avoir
 wt_node à chaque fois
Voir avec Basile :
 pourquoi wt_global -> Ordered_nodes ?
On voudrait un wt_global plus faible mais plus
 facile à manipuler (pas de Forall' !!)
on réserve le Ordered_nodes pour les raisonnements inductifs
 *)
Lemma sem_global_absent :
  forall {PSyn Prefs} (G : @global PSyn Prefs),
    restr_global G ->
    wt_global G ->
    sem_global_abs G.
Proof.
  intros ?? [tys exts nds] Hr Hwt.
  induction nds as [| n' nds]; intros f n Hfind ??. inv Hfind.
  apply wt_global_wl_global in Hwt as Hord.
  apply wl_global_Ordered_nodes in Hord.
  destruct (ident_eq_dec f (n_name n')); subst.
  rewrite find_node_now in Hfind; auto; inv Hfind.
  { (* FIXME: en extraire un lemme, mais comment ? *)
  subst ss os.
  eapply Snode with (H := fun _ => Some (Streams.const absent));
    eauto using find_node_now.
  + (* ins *)
    apply Forall2_forall2; unfold idents.
    rewrite map_length, repeat_length.
    split; intros; subst; auto.
    econstructor; eauto.
    rewrite nth_repeat_in; now auto.
  + (* outs *)
    apply Forall2_forall2; unfold idents.
    rewrite map_length, repeat_length.
    split; intros; subst; auto.
    econstructor; eauto.
    rewrite nth_repeat_in; now auto.
  + (* bloc *)
    apply sem_block_cons'; eauto using find_node_not_Is_node_in, find_node_now.
    inv Hr. take (restr_node _) and inversion_clear it as [?? Hr (?&?&?)].
    inversion Hr as [ vars ??? Hn].
    apply wt_global_cons in Hwt as Hwt'.
    apply wt_global_uncons in Hwt. inversion_clear Hwt as [????? Hwt''].
    rewrite <- Hn in *.
    inv Hwt''.
    take (wt_scope _ _ _ _) and inv it.
    constructor.
    (* scope *)
    apply Sscope with (Hi' := abs_hist_of_vars vars);
      auto using abs_hist_of_vars_dom.
    simpl_Forall.
    apply sem_block_refines with (H := fun _ => Some (Streams.const absent)).
    { intros ?? Eq. inv Eq.
      do 2 esplit. reflexivity.
      destruct (abs_hist_of_vars vars x1) eqn:Find2.
      - apply FEnv.union1; auto.
        unfold abs_hist_of_vars in *. cases.
      - apply FEnv.union2; auto. }
    take (restr_block _) and  inv it.
    take (wt_block _ _ _) and inv it.
    take (wt_equation _ _ _) and inv it.
    constructor.
    (* equation *)
    apply Seq with
      (ss := List.map (fun e => repeat (Streams.const absent) (numstreams e)) es); simpl.
    (* expressions *)
    rewrite clocks_of_false2.
    match goal with H:Forall (wt_exp _ ?Γ) _ |- _=> revert H; generalize Γ end.
    intros; clear dependent n.
    clear dependent blks.
    induction es; simpl_Forall; constructor; eauto.
    eapply sem_exp_absent; now eauto.
    (* variables *)
    assert (length xs = list_sum (List.map numstreams es)) as Hl.
    { rewrite <- annots_numstreams, <- length_typesof_annots.
      eauto using Forall2_length. }
    clear - Hl. revert dependent xs.
    induction es; simpl; intros.
    * destruct xs; simpl in *; auto; congruence.
    * apply length_app_decomp in Hl as (xs1 & xs2 & ? & Hl1 & Hl2); subst.
      apply Forall2_app; auto.
      rewrite <- Hl1; clear.
      induction xs1; simpl; constructor; auto.
      now econstructor.
  }
  rewrite find_node_other in Hfind; auto.
  inv Hr; apply wt_global_cons in Hwt.
  unfold sem_global_abs in IHnds.
  apply sem_node_cons'; eauto.
Qed.

End Sem_absent.


(** ** Translation of [DS (sampl value)] to [Stream svalue]  *)

Definition sval_of_sampl : sampl value -> svalue :=
  fun v => match v with
        | pres v => present v
        | abs => absent
        | err e => absent
        end.

Definition S_of_DSv := S_of_DS sval_of_sampl.

Lemma S_of_DSv_eq :
  forall (s : DS (sampl value)) Hs t (Heq : s == t),
  exists Ht,
    S_of_DSv s Hs ≡ S_of_DSv t Ht.
Proof.
  esplit.
  apply (__S_of_DS_eq _ _ Hs _ Heq).
Qed.

Lemma tl_rem :
  forall s Inf Inf',
    Streams.tl (S_of_DSv s Inf) ≡ S_of_DSv (REM _ s) Inf'.
Proof.
  intros.
  apply infinite_decomp in Inf as HH.
  destruct HH as (h & t & Hs & Inf3).
  edestruct (S_of_DSv_eq) as [? ->]; [ apply Hs |].
  edestruct (S_of_DSv_eq) as [? Eq2].
  2: setoid_rewrite Eq2 at 2.
  rewrite Hs, REM_simpl, rem_cons; reflexivity.
  unfold S_of_DSv.
  rewrite S_of_DS_cons; simpl.
  now apply _S_of_DS_eq.
Qed.

(** *** lift S_of_DSv on lists of streams *)
Definition Ss_of_nprod {n} (np : @nprod (DS (sampl value)) n)
  (Hinf : forall_nprod (@infinite _) np) : list (Stream svalue).
  induction n.
  - exact [].
  - exact (S_of_DSv (nprod_hd np) (forall_nprod_hd _ _ Hinf)
             :: IHn (nprod_tl np) (forall_nprod_tl _ _ Hinf)).
Defined.

Lemma Ss_of_nprod_length :
  forall n (np : nprod n) infn,
    length (Ss_of_nprod np infn) = n.
Proof.
  induction n; simpl; eauto.
Qed.

Lemma _Ss_of_nprod_eq :
  forall n (np np' : nprod n) Hinf Hinf',
    np == np' ->
    EqSts (Ss_of_nprod np Hinf) (Ss_of_nprod np' Hinf').
Proof.
  induction n; intros * Heq.
  - constructor.
  - constructor.
    + now apply _S_of_DS_eq; rewrite Heq.
    + now apply IHn; rewrite Heq.
Qed.

(* utilisation : edestruct (Ss_of_nprod_eq _ Hinf) as [Inf' ->] *)
Corollary Ss_of_nprod_eq :
  forall {n} (np : nprod n) Hinf np',
    np == np' ->
    exists Hinf',
      EqSts (Ss_of_nprod np Hinf) (Ss_of_nprod np' Hinf').
Proof.
  intros * Heq.
  assert (forall_nprod (@infinite _) np') as H by now rewrite <- Heq.
  exists H. now apply _Ss_of_nprod_eq.
Qed.

(* utilisation : edestruct Ss_of_nprod_nth as [Inf' ->] *)
Lemma Ss_of_nprod_nth :
  forall n (np : nprod n) Inf k d s,
    k < n ->
    exists Inf2,
      nth k (Ss_of_nprod np Inf) s ≡ S_of_DSv (get_nth k d np) Inf2.
Proof.
  intros * Hk.
  exists (forall_nprod_k _ _ Inf k d Hk).
  revert_all.
  induction n; intros.
  - inv Hk.
  - destruct k; simpl.
    + now apply _S_of_DS_eq.
    + unshelve erewrite IHn; auto with arith.
      now apply _S_of_DS_eq.
Qed.

Lemma _Ss_app :
  forall n m (np : nprod n) (mp : nprod m) Hnm Hn Hm,
    EqSts (Ss_of_nprod (nprod_app np mp) Hnm)
      ((Ss_of_nprod np Hn) ++ (Ss_of_nprod mp Hm)).
Proof.
  intros.
  induction n; simpl; intros.
  - apply _Ss_of_nprod_eq; auto.
  - constructor.
    + apply _S_of_DS_eq.
      now setoid_rewrite nprod_hd_app.
    + destruct n.
      * destruct m; constructor; auto.
        apply _S_of_DS_eq; auto.
        apply _Ss_of_nprod_eq; auto.
      * setoid_rewrite <- IHn.
        apply _Ss_of_nprod_eq; auto.
  Unshelve.
  apply forall_nprod_app; auto.
  now apply forall_nprod_tl in Hn.
Qed.

Corollary Ss_app :
  forall {n m} (np : nprod n) (mp : nprod m) Hnm,
  exists Hn Hm,
    EqSts (Ss_of_nprod (nprod_app np mp) Hnm)
      ((Ss_of_nprod np Hn) ++ (Ss_of_nprod mp Hm)).
Proof.
  intros.
  destruct (app_forall_nprod _ _ _ Hnm) as [Hn Hm].
  exists Hn,Hm.
  apply _Ss_app.
Qed.

Lemma Ss_map :
  forall f (g : DS (sampl value) -C-> DS (sampl value)),
    (forall x Inf Inf', f (S_of_DSv x Inf) ≡ S_of_DSv (g x) Inf') ->
    forall n (np : nprod n) Inf Inf',
      EqSts (map f (Ss_of_nprod np Inf)) (Ss_of_nprod (lift g np) Inf').
Proof.
  intros * Hfg.
  induction n; constructor.
  - rewrite Hfg.
    apply _S_of_DS_eq.
    now rewrite lift_hd.
  - erewrite IHn.
    erewrite _Ss_of_nprod_eq.
    2:{ rewrite <- lift_tl; reflexivity. }
    reflexivity.
    Unshelve.
    * apply forall_nprod_hd in Inf'; now rewrite lift_hd in Inf'.
    * apply forall_nprod_lift in Inf'.
      now apply forall_nprod_lift, forall_nprod_tl.
Qed.

Lemma Ss_of_nprod_hds :
  forall n (np : @nprod (DS (sampl value)) n) npc npi,
    map sval_of_sampl (nprod_hds np npc) = map (@Streams.hd _) (Ss_of_nprod np npi).
Proof.
  induction n; intros; auto.
  simpl (nprod_hds _ _).
  simpl (Ss_of_nprod _ _).
  destruct (uncons _) as (?&?& Hd).
  simpl (map sval_of_sampl _).
  apply decomp_eqCon in Hd.
  edestruct (S_of_DSv_eq) as [Inf ->]; [apply Hd|].
  unfold S_of_DSv.
  rewrite S_of_DS_cons.
  simpl; f_equal; auto.
Qed.

(** comment passer de denot_exps à (concat denot_exp) *)
Lemma Ss_exps :
  forall {PSyn Prefs} (G : @global PSyn Prefs),
  forall ins envG envI env es Hinf Infe,
    EqSts (Ss_of_nprod (denot_exps G ins es envG envI env) Hinf)
      (flat_map (fun e => Ss_of_nprod (denot_exp G ins e envG envI env) (Infe e)) es).
Proof.
  induction es; intros; simpl.
  constructor.
  edestruct (Ss_of_nprod_eq _ Hinf) as [Inf' ->].
  { rewrite denot_exps_eq; reflexivity. }
  setoid_rewrite (ex_proj2 (ex_proj2 (Ss_app _ _ _))).
  apply app_EqSts; auto.
  now apply _Ss_of_nprod_eq.
Qed.


(** *** lift Ss_of_nprod on matrix of streams *)
Fixpoint Ss_of_nprods {n m} (nmp : @nprod (@nprod (DS (sampl value)) m) n) :
  forall_nprod (forall_nprod (@infinite _)) nmp -> list (list (Stream svalue)) :=
  match n return forall (nmp : nprod n), (forall_nprod (forall_nprod (@infinite _)) nmp) -> _ with
  | O => fun _ _ => []
  | S n => fun nmp Inf =>
            Ss_of_nprod (nprod_hd nmp) (forall_nprod_hd _ _ Inf)
              :: Ss_of_nprods (nprod_tl nmp) (forall_nprod_tl _ _ Inf)
  end nmp.

Lemma _Ss_of_nprods_eq :
  forall n m (np1 np2 : @nprod (@nprod (DS (sampl value)) m) n) Inf1 Inf2,
    np1 == np2 ->
    Forall2 EqSts (Ss_of_nprods np1 Inf1) (Ss_of_nprods np2 Inf2).
Proof.
  induction n; intros * Heq; constructor.
  - apply _Ss_of_nprod_eq.
    now rewrite Heq.
  - apply IHn.
    now rewrite Heq.
Qed.

Lemma Ss_of_nprods_hd :
  forall d n m (vss : @nprod (nprod (S m)) n) Inf1 Inf2,
    EqSts (map (hd d) (Ss_of_nprods vss Inf1))
      (Ss_of_nprod (lift nprod_hd vss) Inf2).
Proof.
  induction n; intros.
  - constructor.
  - constructor.
    + apply _S_of_DS_eq.
      now rewrite lift_hd.
    + unshelve rewrite IHn.
      { apply forall_nprod_lift in Inf2.
        now apply forall_nprod_lift, forall_nprod_tl. }
      apply _Ss_of_nprod_eq.
      now rewrite lift_tl.
Qed.

Lemma Ss_of_nprods_tl :
  forall n m (vss : @nprod (nprod (S m)) n) Inf1 Inf2,
    Forall2 EqSts (map (@tl _) (Ss_of_nprods vss Inf1))
      (Ss_of_nprods (lift nprod_tl vss) Inf2).
Proof.
  induction n; intros.
  - constructor.
  - constructor.
    + apply _Ss_of_nprod_eq.
      now rewrite lift_hd.
    + unshelve rewrite IHn.
      { apply forall_nprod_lift in Inf2.
        now apply forall_nprod_lift, forall_nprod_tl. }
      apply _Ss_of_nprods_eq.
      now rewrite lift_tl.
Qed.

Generalizable All Variables.
Lemma Forall2t_lift_nprod :
  forall (* (P : list (Stream svalue) -> Stream svalue -> Prop) *)
    `{ (Proper (Forall2 (@EqSt _) ==> @EqSt _ ==> Basics.impl) P)%signature },
  forall n (F : nprod n -C-> DS (sampl value)),
  forall (Q : DS (sampl value) -> Prop),
    (forall (np : nprod n) Inf1 Inf2, Q (F np) -> P (Ss_of_nprod np Inf1) (S_of_DSv (F np) Inf2)) ->
    forall d m (vss : @nprod (@nprod (DS (sampl value)) m) n) Inf1 Inf2,
      forall_nprod Q (lift_nprod F vss) ->
      Forall2t d P (Ss_of_nprods vss Inf1) (Ss_of_nprod (lift_nprod F vss) Inf2).
Proof.
  intros ?? * QP d.
  induction m; intros * Hq.
  - constructor.
    clear; induction n; simpl; auto.
  - constructor.
    + edestruct (S_of_DSv_eq) as [Inf3 ->].
      { rewrite hd_lift_nprod; reflexivity. }
      unshelve rewrite Ss_of_nprods_hd; eauto.
      { eapply forall_nprod_lift, forall_nprod_impl; eauto.
        apply forall_nprod_hd. }
      apply forall_nprod_hd in Hq.
      rewrite hd_lift_nprod in Hq.
      apply (QP _ _ _ Hq).
    + edestruct (Ss_of_nprod_eq ((nprod_tl (lift_nprod F vss)))) as [Inf3 ->].
      { rewrite tl_lift_nprod; reflexivity. }
      unshelve rewrite Ss_of_nprods_tl.
      { eapply forall_nprod_lift, forall_nprod_impl; eauto.
        apply forall_nprod_tl. }
      eapply IHm; eauto.
      rewrite <- tl_lift_nprod.
      now apply forall_nprod_tl.
Qed.

(** comment passer de denot_expss à (map _ (concat denot_exp)) *)
Lemma Ss_expss :
  forall {PSyn Prefs} (G : @global PSyn Prefs),
  forall ins envG envI env (ess : list (enumtag * (list exp))) n Infe Inf,
    Forall (fun es => list_sum (map numstreams (snd es)) = n) ess ->
    Forall2 EqSts
      (map
         (flat_map
            (fun e => Ss_of_nprod (denot_exp G ins e envG envI env) (Infe e))) (map snd ess))
      (Ss_of_nprods (denot_expss G ins ess n envG envI env) Inf).
Proof.
  induction ess as [| (i,es) ess]; intros * Hl. { constructor. }
  inv Hl.
  revert Inf.
  match goal with
  | |- context [ ?f1 (?f2 (?f3 (denot_expss ?e1 ?e2 ?e3 ?e4) ?e5) ?e6) ?e7 ] =>
      remember (f1 (f2 (f3 (denot_expss e1 e2 e3 e4) e5) e6) e7) as t eqn:Ht
  end.
  setoid_rewrite denot_expss_eq in Ht.
  unfold eq_rect in Ht.
  cases; try (simpl in *; congruence).
  subst; intros; constructor.
  - unshelve rewrite <- Ss_exps.
    { now apply forall_nprod_cons_iff in Inf as []. }
    apply _Ss_of_nprod_eq.
    now rewrite nprod_hd_cons.
  - (* pour réécrire [nprod_tl_app_1] et utiliser IHess, il faut que le
       membre droit du nprod_app soit de taille > 0. On doit donc détruire
       ess une fois de plus. *)
    destruct ess as [|(j,es2) ess]. { now constructor. }
    setoid_rewrite <- IHess; eauto.
    constructor; reflexivity.
Qed.

(** ** Correspondence of semantic predicate for streams functions *)

(** In the lext lemmas we use the method of coinduction loading from
    "Circular coinduction in Coq using bisimulation-up-to techniques" by
    Endrullis, Hendriks and Bodin.
    Their idea is to push computation/rewriting in the arguments of the
    coinductive predicate instead of performing it at top-level, which
    would breaks Coq guardedness condition. Thus, instead of proving
      forall xs ys, P xs ys
    we prove
      forall xs ys, forall xs' ys', xs ≡ xs' -> ys ≡ ys' -> P xs' ys'
 *)

Lemma ok_const :
  forall c bs Hinf,
    S_of_DSv (sconst (Vscalar (sem_cconst c)) (DS_of_S bs)) Hinf ≡ const bs c.
Proof.
  intros.
  remember_st (S_of_DSv _ Hinf) as xs.
  remember_st (const bs c) as ys.
  revert_all.
  cofix Cof; intros * Eqx ? Eqy.
  destruct xs as [vx xs], ys as [vy ys], bs as [b bs].
  apply S_of_DS_Cons in Eqx as (x & tx & Hxs & Hxvx & itx & Eqx).
  setoid_rewrite unfold_Stream in Eqy.
  setoid_rewrite DS_inv in Hxs at 2; simpl in *.
  unfold sconst in *.
  rewrite MAP_map, Cpo_streams_type.map_eq_cons in Hxs.
  apply Con_eq_simpl in Hxs as [? Heq]; subst; simpl.
  inv Eqy; simpl in *; subst.
  constructor; simpl; cases.
  rewrite (ex_proj2 (S_of_DS_eq _ _ _ _ (symmetry Heq))) in Eqx; eauto.
Qed.

Lemma ok_enum :
  forall c bs Hinf,
    S_of_DSv (sconst (Venum c) (DS_of_S bs)) Hinf ≡ enum bs c.
Proof.
  intros.
  remember_st (S_of_DSv _ Hinf) as xs.
  remember_st (enum bs c) as ys.
  revert_all.
  cofix Cof; intros * Eqx ? Eqy.
  destruct xs as [vx xs], ys as [vy ys], bs as [b bs].
  apply S_of_DS_Cons in Eqx as (x & tx & Hxs & Hxvx & itx & Eqx).
  setoid_rewrite unfold_Stream in Eqy.
  setoid_rewrite DS_inv in Hxs at 2; simpl in *.
  unfold sconst in *.
  rewrite MAP_map, Cpo_streams_type.map_eq_cons in Hxs.
  apply Con_eq_simpl in Hxs as [? Heq]; subst; simpl.
  inv Eqy; simpl in *; subst.
  constructor; simpl; cases.
  rewrite (ex_proj2 (S_of_DS_eq _ _ _ _ (symmetry Heq))) in Eqx; eauto.
Qed.

Lemma ok_unop :
  forall op ty (xs : DS (sampl value)),
    let rs := sunop (fun v => sem_unop op v ty) xs in
    forall (xsi : infinite xs)
      (rsi : infinite rs),
      safe_DS rs ->
      lift1 op ty (S_of_DSv xs xsi) (S_of_DSv rs rsi).
Proof.
  intros.
  remember_st (S_of_DSv xs xsi) as xs'.
  remember_st (S_of_DSv rs rsi) as rs'.
  revert_all.
  cofix Cof; intros * Sr ? Eqx ? Eqr.
  destruct xs' as [vx xs'], rs' as [vr rs'].
  apply S_of_DS_Cons in Eqx as (x & tx & Hxs & Hxvx & itx & Eqx).
  apply S_of_DS_Cons in Eqr as (r & tr & Hrs & Hrvr & itr & Eqr).
  subst rs.
  rewrite Hxs, sunop_eq in Hrs, Sr.
  cases_eqn HH; simpl; try now inv Sr.
  all: apply Con_eq_simpl in Hrs as [? Heq]; subst; simpl.
  all: constructor; eauto.
  all: apply DSForall_tl in Sr.
  all: rewrite (ex_proj2 (S_of_DS_eq _ _ _ _ (symmetry Heq))) in Eqr; eauto.
Qed.

Lemma ok_binop :
  forall op ty1 ty2 (xs ys : DS (sampl value)),
    let rs := sbinop (fun v1 v2 => sem_binop op v1 ty1 v2 ty2) xs ys in
    forall (xsi : infinite xs)
      (ysi : infinite ys)
      (rsi : infinite rs),
      safe_DS rs ->
      lift2 op ty1 ty2 (S_of_DSv xs xsi) (S_of_DSv ys ysi) (S_of_DSv rs rsi).
Proof.
  intros.
  remember_st (S_of_DSv xs xsi) as xs'.
  remember_st (S_of_DSv ys ysi) as ys'.
  remember_st (S_of_DSv rs rsi) as rs'.
  revert_all.
  cofix Cof; intros * Sr ? Eqx ? Eqy ? Eqr.
  destruct xs' as [vx xs'], ys' as [vy ys'], rs' as [vr rs'].
  apply S_of_DS_Cons in Eqx as (x & tx & Hxs & Hxvx & itx & Eqx).
  apply S_of_DS_Cons in Eqy as (y & ty & Hys & Hyvy & ity & Eqy).
  apply S_of_DS_Cons in Eqr as (r & tr & Hrs & Hrvr & itr & Eqr).
  subst rs.
  rewrite Hxs, Hys, sbinop_eq in Hrs, Sr.
  cases_eqn HH; simpl; try now inv Sr.
  all: apply Con_eq_simpl in Hrs as [? Heq]; subst; simpl.
  all: constructor; eauto.
  all: apply DSForall_tl in Sr.
  all: rewrite (ex_proj2 (S_of_DS_eq _ _ _ _ (symmetry Heq))) in Eqr; eauto.
Qed.

Lemma ok_fby1 :
  forall v (xs ys : DS (sampl value)),
    let rs := SDfuns.fby1 (Some v) xs ys in
    forall (xsi : infinite xs)
      (ysi : infinite ys)
      (rsi : infinite rs),
      safe_DS rs ->
      fby1 v (S_of_DSv xs xsi) (S_of_DSv ys ysi) (S_of_DSv rs rsi).
Proof.
  intros.
  remember_st (S_of_DSv xs xsi) as xs'.
  remember_st (S_of_DSv ys ysi) as ys'.
  remember_st (S_of_DSv rs rsi) as rs'.
  revert_all.
  cofix Cof; intros * Sr ? Eqx ? Eqy ? Eqr.
  destruct xs' as [vx xs'], ys' as [vy ys'], rs' as [vr rs'].
  apply S_of_DS_Cons in Eqx as (x & tx & Hxs & Hxvx & itx & Eqx).
  apply S_of_DS_Cons in Eqy as (y & ty & Hys & Hyvy & ity & Eqy).
  apply S_of_DS_Cons in Eqr as (r & tr & Hrs & Hrvr & itr & Eqr).
  subst rs.
  rewrite Hxs, Hys, fby1_eq in Hrs, Sr.
  destruct x, y; simpl in *; subst; inversion_clear Sr as [|??? Sr']; try tauto.
  all: apply Con_eq_simpl in Hrs as [? Heq]; subst; simpl.
  all: rewrite fby1AP_eq in Heq, Sr'.
  (* pour les cas d'erreur, il faut un con de plus : *)
  all: try (clear - Sr' itx;
            apply infinite_decomp in itx as (?&?& Htx &?);
            rewrite Htx, Cpo_streams_type.map_eq_cons in Sr'; now inv Sr').
  all: rewrite (ex_proj2 (S_of_DS_eq _ _ _ _ (symmetry Heq))) in Eqr; eauto.
  all: constructor; eapply Cof; eauto.
Qed.

Lemma ok_fby :
  forall (xs ys : DS (sampl value)),
    let rs := SDfuns.fby xs ys in
    forall (xsi : infinite xs)
      (ysi : infinite ys)
      (rsi : infinite rs),
      safe_DS rs ->
      fby (S_of_DSv xs xsi) (S_of_DSv ys ysi) (S_of_DSv rs rsi).
Proof.
  intros.
  remember_st (S_of_DSv xs xsi) as xs'.
  remember_st (S_of_DSv ys ysi) as ys'.
  remember_st (S_of_DSv rs rsi) as rs'.
  revert_all.
  cofix Cof; intros * Sr ? Eqx ? Eqy ? Eqr.
  destruct xs' as [vx xs'], ys' as [vy ys'], rs' as [vr rs'].
  apply S_of_DS_Cons in Eqx as (x & tx & Hxs & Hxvx & itx & Eqx).
  apply S_of_DS_Cons in Eqy as (y & ty & Hys & Hyvy & ity & Eqy).
  apply S_of_DS_Cons in Eqr as (r & tr & Hrs & Hrvr & itr & Eqr).
  subst rs.
  rewrite Hxs, Hys, fby_eq in Hrs, Sr.
  destruct x, y; simpl in *; subst; inversion_clear Sr as [|??? Sr']; try tauto.
  all: apply Con_eq_simpl in Hrs as [? Heq]; subst; simpl.
  all: rewrite ?fbyA_eq, ?fby1AP_eq in Heq, Sr'.
  (* pour les cas d'erreur, il faut un con de plus : *)
  all: try (clear - Sr' itx;
            apply infinite_decomp in itx as (?&?& Htx &?);
            rewrite Htx, Cpo_streams_type.map_eq_cons, ?fby1_eq, ?fby_eq in Sr'; now inv Sr').
  all: rewrite (ex_proj2 (S_of_DS_eq _ _ _ _ (symmetry Heq))) in Eqr; eauto.
  all: constructor; eauto.
  rewrite <- Eqr, <- Eqx, <- Eqy.
  apply ok_fby1; auto.
Qed.

Lemma ok_when :
  forall k (xs cs : DS (sampl value)),
    let rs := swhenv k xs cs in
    forall (xsi : infinite xs)
      (csi : infinite cs)
      (rsi : infinite rs),
      safe_DS rs ->
      when k (S_of_DSv xs xsi) (S_of_DSv cs csi) (S_of_DSv rs rsi).
Proof.
  intros.
  remember_st (S_of_DSv xs xsi) as xs'.
  remember_st (S_of_DSv cs csi) as cs'.
  remember_st (S_of_DSv rs rsi) as rs'.
  revert_all.
  cofix Cof; intros * Sr ? Eqx ? Eqc ? Eqr.
  destruct xs' as [vx xs'], cs' as [vc cs'], rs' as [vr rs'].
  apply S_of_DS_Cons in Eqx as (x & tx & Hxs & Hxvx & itx & Eqx).
  apply S_of_DS_Cons in Eqc as (c & tc & Hcs & Hcvc & itc & Eqc).
  apply S_of_DS_Cons in Eqr as (r & tr & Hrs & Hrvr & itr & Eqr).
  subst rs.
  unfold swhenv in *; rewrite Hxs, Hcs, swhen_eq in Hrs.
  cases_eqn HH; simpl in *; subst; try take (Some _ = Some _) and inv it.
  all: try apply Con_eq_simpl in Hrs as [? Heq]; subst; simpl.
  all: rewrite Hxs, Hcs in *.
  all: rewrite swhen_eq in Sr, rsi.
  (* error cases *)
  all: try (inv Sr; tauto).
  2: assert (k = e) by (now apply Nat.eqb_eq); subst.
  all: econstructor; auto using (proj1 (Nat.eqb_neq _ _)).
  all: rewrite (ex_proj2 (S_of_DS_eq _ _ _ _ (symmetry Heq))) in Eqr; eauto.
  all: cases; try easy; inv Sr; eauto.
Qed.

Lemma ok_merge :
  forall l (cs : DS (sampl value)) (np : nprod (length l)),
    let rs := smergev l cs np in
    forall (npi : forall_nprod (@infinite _) np)
      (csi : infinite cs)
      (rsi : infinite rs),
      safe_DS rs ->
      merge (S_of_DSv cs csi) (combine l (Ss_of_nprod np npi)) (S_of_DSv rs rsi).
Proof.
  intros.
  remember_st (S_of_DSv cs csi) as cs'.
  remember_st (S_of_DSv rs rsi) as rs'.
  remember_sts (Ss_of_nprod np npi) as np'.
  revert_all; intro l.
  cofix Cof; intros * Sr ? Eqc ? Eqr ? Eqnp. (* ? Eqx. *)
  destruct cs' as [vc cs'], rs' as [vr rs'].
  apply S_of_DS_Cons in Eqc as (c & tc & Hcs & Hcvc & itc & Eqc).
  apply S_of_DS_Cons in Eqr as (r & tr & Hrs & Hrvr & itr & Eqr).
  (* on fait tout de suite le cas de récurrence *)
  assert (merge cs' (map (fun '(i, es) => (i, Streams.tl es)) (combine l np')) rs').
  { replace (map  _ (combine l np')) with (combine l (map (@Streams.tl _) np')).
    2: rewrite combine_map_snd; apply map_ext; now intros [].
    apply forall_nprod_impl with (Q := fun x => infinite (REM _ x))
      in npi as np'i; [|apply rem_infinite].
    apply forall_nprod_lift in np'i.
    apply DSForall_rem in Sr.
    apply rem_eq_compat in Hcs, Hrs.
    unfold smergev in rs; subst rs.
    rewrite rem_smerge, rem_cons in *.
    unshelve eapply Cof with (cs := rem cs) (np := lift _ _);
      eauto using rem_infinite, smerge_inf.
    - rewrite <- Eqc; eauto using _S_of_DS_eq.
    - rewrite <- Eqr; eauto using _S_of_DS_eq.
    - rewrite <- Eqnp.
      rewrite Ss_map; auto using tl_rem; reflexivity. }
  rewrite Hrs in *; inv Sr.
  subst rs.
  unfold smergev in Hrs.
  assert (forall_nprod (@is_cons _) np) as npc.
  { clear - npi. eapply forall_nprod_impl in npi; eauto. now inversion 1. }
  rewrite Hcs, (smerge_cons _ _ _ _ _ _ _ npc) in Hrs.
  apply Con_eq_simpl in Hrs as [Hr Heq].
  destruct r; simpl in *; subst; try tauto.
  - (* absent *)
    apply fmerge_abs in Hr as [? Hf]; subst.
    constructor; auto.
    apply Forall2_combine'' in Hf; auto using hds_length.
    apply Forall2_combine'; simpl.
    apply (Forall2_map_2 (fun _ x => x = absent) (@Streams.hd _)).
    rewrite <- Eqnp, <- (Ss_of_nprod_hds _ _ npc).
    simpl_Forall; subst; auto.
  - (* present *)
    apply fmerge_pres in Hr as ([] &?&? & Hx & Hex & Hf); subst;
      auto using Nat.eqb_eq; try congruence.
    inversion Hx; subst.
    constructor; auto.
    + (* Exists *)
      clear - Eqnp Hex npc.
      eapply Exists_impl,
        (Exists_map (fun '(t,s) => (t, @Streams.hd _ s)) (fun '(i,es) => i = x /\ es = present a)).
      intros []; auto.
      rewrite map_ext with (g := fun c => (fst c, Streams.hd (snd c))), <- combine_map_snd.
      2: intros []; auto.
      pose proof (Ss_of_nprod_hds _ _ npc npi) as HH.
      rewrite Eqnp in HH.
      setoid_rewrite <- HH.
      rewrite combine_map_snd, Exists_map.
      eapply Exists_impl; eauto.
      unfold sval_of_sampl; now intros [] []; subst.
    + (* Forall *)
      apply Forall2_combine'' in Hf; auto using hds_length.
      apply Forall2_combine'; simpl.
      apply (Forall2_map_2 (fun _ x => _ -> x = absent) (@Streams.hd _)).
      rewrite <- Eqnp, <- (Ss_of_nprod_hds _ _ npc).
      simpl_Forall; unfold sval_of_sampl; cases.
      clear - H4 H5; firstorder congruence.
Qed.

Lemma ok_case :
  forall l, l <> [] ->
  forall (cs : DS (sampl value)) (np : nprod (length l)),
    let rs := scasev l cs np in
    forall (npi : forall_nprod (@infinite _) np)
      (csi : infinite cs)
      (rsi : infinite rs),
      safe_DS rs ->
      case (S_of_DSv cs csi) (combine l (Ss_of_nprod np npi)) None (S_of_DSv rs rsi).
Proof.
  intros.
  remember_st (S_of_DSv cs csi) as cs'.
  remember_st (S_of_DSv rs rsi) as rs'.
  remember_sts (Ss_of_nprod np npi) as np'.
  revert_all; intros l Nnil.
  cofix Cof; intros * Sr ? Eqc ? Eqr ? Eqnp. (* ? Eqx. *)
  destruct cs' as [vc cs'], rs' as [vr rs'].
  apply S_of_DS_Cons in Eqc as (c & tc & Hcs & Hcvc & itc & Eqc).
  apply S_of_DS_Cons in Eqr as (r & tr & Hrs & Hrvr & itr & Eqr).
  (* on fait tout de suite le cas de récurrence *)
  assert (case cs' (map (fun '(i, es) => (i, Streams.tl es)) (combine l np')) None rs').
  { replace (map  _ (combine l np')) with (combine l (map (@Streams.tl _) np')).
    2: rewrite combine_map_snd; apply map_ext; now intros [].
    apply forall_nprod_impl with (Q := fun x => infinite (REM _ x))
      in npi as np'i; [|apply rem_infinite].
    apply forall_nprod_lift in np'i.
    apply DSForall_rem in Sr.
    apply rem_eq_compat in Hcs, Hrs.
    unfold scasev in rs; subst rs.
    rewrite rem_scase, rem_cons in *.
    unshelve eapply Cof with (cs := rem cs) (np := lift _ _);
      eauto using rem_infinite, scase_inf.
    - rewrite <- Eqc; eauto using _S_of_DS_eq.
    - rewrite <- Eqr; eauto using _S_of_DS_eq.
    - rewrite <- Eqnp.
      rewrite Ss_map; auto using tl_rem; reflexivity. }
  rewrite Hrs in *; inv Sr.
  subst rs.
  unfold scasev in Hrs.
  assert (forall_nprod (@is_cons _) np) as npc.
  { clear - npi. eapply forall_nprod_impl in npi; eauto. now inversion 1. }
  rewrite Hcs, (scase_cons _ _ _ _ _ _ _ npc) in Hrs.
  apply Con_eq_simpl in Hrs as [Hr Heq].
  destruct r; simpl in *; subst; try tauto.
  - (* absent *)
    apply fcase_abs in Hr as (?&?& Hf); subst.
    2: clear Cof H; destruct l; simpl in *; congruence.
    constructor; auto.
    apply Forall2_combine'' in Hf; auto using hds_length.
    apply Forall2_combine'; simpl.
    apply (Forall2_map_2 (fun _ x => x = absent) (@Streams.hd _)).
    rewrite <- Eqnp, <- (Ss_of_nprod_hds _ _ npc).
    simpl_Forall; subst; auto.
  - (* present *)
    apply fcase_pres in Hr as ([] &?&? & Hx & Hex & Hf); subst;
      auto using Nat.eqb_eq; try congruence.
    inversion Hx; subst.
    constructor; auto.
    + (* Forall *)
      apply Forall2_combine'', Forall2_ignore1'' in Hf; auto using hds_length.
      apply Forall2_combine'; simpl.
      apply Forall2_ignore1'.
      { now rewrite <- Eqnp, Ss_of_nprod_length. }
      eapply (Forall_map _ (fun x => x <> absent)).
      rewrite <- Eqnp, <- (Ss_of_nprod_hds _ _ npc).
      simpl_Forall; unfold sval_of_sampl; cases; congruence.
    + (* Exists *)
      clear - Eqnp Hex npc.
      eapply Exists_impl,
        (Exists_map (fun '(t,s) => (t, @Streams.hd _ s)) (fun '(i,es) => i = x /\ es = present a)).
      intros []; auto.
      rewrite map_ext with (g := fun c => (fst c, Streams.hd (snd c))), <- combine_map_snd.
      2: intros []; auto.
      pose proof (Ss_of_nprod_hds _ _ npc npi) as HH.
      rewrite Eqnp in HH.
      setoid_rewrite <- HH.
      rewrite combine_map_snd, Exists_map.
      eapply Exists_impl; eauto.
      unfold sval_of_sampl; now intros [] []; subst.
Qed.

Lemma ok_case_def :
  forall l, l <> [] ->
  forall (cs : DS (sampl value)) (dnp : nprod (S (length l))),
    let rs := scase_defv l cs dnp in
    let ds := nprod_hd dnp in
    let np := nprod_tl dnp in
    forall (npi : forall_nprod (@infinite _) np)
      (csi : infinite cs)
      (dsi : infinite ds)
      (rsi : infinite rs),
      safe_DS rs ->
      case (S_of_DSv cs csi) (combine l (Ss_of_nprod np npi)) (Some (S_of_DSv ds dsi)) (S_of_DSv rs rsi).
Proof.
  intros l Nnil cs dnp.
  (* d'abord, mettons [rs] sous la forme [scase_def_ l cs ds np] *)
  rewrite (nprod_hd_tl dnp), nprod_hd_cons.
  intros rs ds' np'.
  assert (np' = nprod_tl dnp) as Hnp.
  { destruct l; try congruence; subst np'.
    now rewrite nprod_tl_cons with (np := nprod_tl dnp). }
  revert rs.
  rewrite <- Hnp; clear Hnp; fold ds'.
  generalize np' as np, ds' as ds; clear - Nnil; intros ???.
  unfold scase_defv in rs; revert rs; rewrite scase_def_eq; intro.
  (* c'est bon *)
  intros.
  remember_st (S_of_DSv cs csi) as cs'.
  remember_st (S_of_DSv ds dsi) as ds'.
  remember_st (S_of_DSv rs rsi) as rs'.
  remember_sts (Ss_of_nprod np npi) as np'.
  revert_all; intros l Nnil.
  cofix Cof; intros * Sr ? Eqc ? Eqd ? Eqr ? Eqnp. (* ? Eqx. *)
  destruct cs' as [vc cs'], ds' as [vd ds'], rs' as [vr rs'].
  apply S_of_DS_Cons in Eqc as (c & tc & Hcs & Hcvc & itc & Eqc).
  apply S_of_DS_Cons in Eqd as (d & td & Hds & Hdvd & itd & Eqd).
  apply S_of_DS_Cons in Eqr as (r & tr & Hrs & Hrvr & itr & Eqr).
  (* on fait tout de suite le cas de récurrence *)
  assert (case cs' (map (fun '(i, es) => (i, Streams.tl es)) (combine l np')) (Some ds') rs').
  { replace (map  _ (combine l np')) with (combine l (map (@Streams.tl _) np')).
    2: rewrite combine_map_snd; apply map_ext; now intros [].
    apply forall_nprod_impl with (Q := fun x => infinite (REM _ x))
      in npi as np'i; [|apply rem_infinite].
    apply forall_nprod_lift in np'i.
    apply DSForall_rem in Sr.
    apply rem_eq_compat in Hcs, Hrs.
    subst rs.
    rewrite rem_scase_def_, rem_cons in *.
    unshelve eapply Cof with (cs := rem cs) (ds := rem ds) (np := lift _ _);
      eauto using rem_infinite, scase_def__inf.
    - rewrite <- Eqc; eauto using _S_of_DS_eq.
    - rewrite <- Eqd; eauto using _S_of_DS_eq.
    - rewrite <- Eqr; eauto using _S_of_DS_eq.
    - rewrite <- Eqnp.
      rewrite Ss_map; auto using tl_rem; reflexivity. }
  rewrite Hrs in *; inv Sr.
  subst rs.
  assert (forall_nprod (@is_cons _) np) as npc.
  { clear - npi. eapply forall_nprod_impl in npi; eauto. now inversion 1. }
  rewrite Hcs, Hds, (scase_def__cons _ _ _ _ _ _ _ _ _ npc) in Hrs.
  apply Con_eq_simpl in Hrs as [Hr Heq].
  destruct r; simpl in *; subst; try tauto.
  - (* absent *)
    apply fcase_abs in Hr as (?&?& Hf); subst.
    2: clear Cof H; destruct l; simpl in *; congruence.
    constructor; auto.
    + apply Forall2_combine'' in Hf; auto using hds_length.
      apply Forall2_combine'; simpl.
      apply (Forall2_map_2 (fun _ x => x = absent) (@Streams.hd _)).
      rewrite <- Eqnp, <- (Ss_of_nprod_hds _ _ npc).
      simpl_Forall; subst; auto.
    + simpl in *; cases.
  - (* present *)
    apply fcase_pres2 in Hr as ([] &?&? & Hx & HH & Hd & Hf & FE); subst;
      auto using Nat.eqb_eq; try congruence.
    2: clear Cof H; destruct l; simpl in *; congruence.
    inv HH.
    (* utile dans les deux cas *)
    assert (Forall (fun es => Streams.hd (snd es) <> absent) (combine l np')) as Hfh.
    { apply Forall2_combine'', Forall2_ignore1'' in Hf; auto using hds_length.
      apply Forall2_combine'; simpl.
      apply Forall2_ignore1'.
      { now rewrite <- Eqnp, Ss_of_nprod_length. }
      eapply (Forall_map _ (fun x => x <> absent)).
      rewrite <- Eqnp, <- (Ss_of_nprod_hds _ _ npc).
      simpl_Forall; unfold sval_of_sampl; cases; congruence. }
    destruct FE as [Hex | [Hfn Hd]].
    * (* la branche est trouvée *)
      apply CaseP; simpl; auto; try congruence.
      clear - Eqnp Hex npc.
      eapply Exists_impl,
        (Exists_map (fun '(t,s) => (t, @Streams.hd _ s)) (fun '(i,es) => i = x0 /\ es = present a)).
      intros []; auto.
      rewrite map_ext with (g := fun c => (fst c, Streams.hd (snd c))), <- combine_map_snd.
      2: intros []; auto.
      pose proof (Ss_of_nprod_hds _ _ npc npi) as HH.
      rewrite Eqnp in HH.
      setoid_rewrite <- HH.
      rewrite combine_map_snd, Exists_map.
      eapply Exists_impl; eauto.
      unfold sval_of_sampl; now intros [] []; subst.
    * (* on utilise la branche par défaut *)
      subst; apply CasePDef; auto.
      apply Forall2_combine'' in Hfn; auto using hds_length.
      apply Forall2_swap_args, Forall2_ignore1'' in Hfn.
      apply Forall2_combine'; simpl.
      apply Forall2_ignore2'; auto.
      now rewrite <- Eqnp, Ss_of_nprod_length.
Qed.

Section BOOLS_OFS.

  (* TODO: move to Vélus ? *)
  Lemma disj_str_orb :
    forall bs bss,
      disj_str [bs; disj_str bss] ≡ map2 orb bs (disj_str bss).
  Proof.
    intros.
    apply ntheq_eqst; intro n.
    rewrite disj_str_spec, Str_nth_map2.
    simpl.
    now rewrite Bool.orb_false_r.
  Qed.

  (* TODO: move to Vélus ? *)
  Lemma bools_ofs_cons :
    forall s ss b bs,
      bools_ofs ss bs ->
      bools_of s b ->
      bools_ofs (s :: ss) (map2 orb b bs).
  Proof.
    unfold bools_ofs.
    intros * (rss & Hf & Hbs) Hb.
    exists (b :: rss); split; auto.
    now rewrite disj_str_cons, Hbs, disj_str_orb.
  Qed.

  Lemma bools_of_sbool_of :
    forall s Inf1 Inf2,
      ty_DS bool_velus_type s ->
      bools_of (S_of_DSv s Inf1) (S_of_DS id (sbool_of s) Inf2).
  Proof.
    unfold ty_DS, sbool_of.
    intros * Hty.
    remember_st (S_of_DSv s Inf1) as u.
    remember_st (S_of_DS id _ Inf2) as v.
    revert_all; cofix Cof; intros.
    destruct u as [u us], v as [v vs].
    apply S_of_DS_Cons in Hu as (?&?& Hs &?&?& Hus); subst.
    apply S_of_DS_Cons in Hv as (?&?& Hbs &?&?& Hvs); subst.
    rewrite Hs, MAP_map, Cpo_streams_type.map_eq_cons in *.
    apply Con_eq_simpl in Hbs as [? Hm]; subst.
    edestruct (S_of_DS_eq id _ x4 _ (symmetry Hm)) as [Inf3 HH].
    rewrite HH in Hvs; clear HH.
    inv Hty.
    cases; try take (wt_value _ _) and inv it; simpl in *; try lia.
    all: constructor; eauto.
  Qed.

  Lemma zip_map2_ :
    forall {A B C} (op : A -> B -> C) s t Inf1 Inf2 Inf3,
      S_of_DS id (ZIP op s t) Inf3 ≡ map2 op (S_of_DS id s Inf1) (S_of_DS id t Inf2).
  Proof.
    intros.
    remember_st (S_of_DS id (ZIP op s t) Inf3) as u.
    remember_st (map2 op (S_of_DS id s Inf1) (S_of_DS id t Inf2)) as v.
    revert_all; cofix Cof; intros.
    destruct u as [u us], v as [v vs].
    apply S_of_DS_Cons in Hu as (?&?& Hz & ? & Infz & Hus); subst.
    apply zip_uncons in Hz as (?&?&?&?& Hs & Ht & Hz &?); subst.
    edestruct (S_of_DS_eq id _ Inf1 _ Hs) as [Inf4 HHs].
    edestruct (S_of_DS_eq id _ Inf2 _ Ht) as [Inf5 HHt].
    rewrite HHs, HHt, 2 S_of_DS_cons in Hv.
    edestruct (S_of_DS_eq id _ Infz _ Hz) as [Inf6 HHz].
    rewrite HHz in Hus.
    inv Hv; simpl in *; subst.
    constructor; simpl; auto.
    eapply Cof; eauto.
  Qed.

  Lemma zip_map2 :
    forall {A B C} (op : A -> B -> C) s t Inf3,
    exists Inf1 Inf2,
      S_of_DS id (ZIP op s t) Inf3 ≡ map2 op (S_of_DS id s Inf1) (S_of_DS id t Inf2).
  Proof.
    clear.
    intros.
    apply inf_zip in Inf3 as HH; destruct HH as [Infs Inft].
    exists Infs, Inft.
    apply zip_map2_.
  Qed.

  Lemma bools_ofs_sbools_of :
    forall n (np : nprod n) Inf1 Inf2,
      forall_nprod (ty_DS bool_velus_type) np ->
      bools_ofs (Ss_of_nprod np Inf1) (S_of_DS id (sbools_of np) Inf2).
  Proof.
    clear.
    intros * Hf.
    edestruct (S_of_DS_eq id _ Inf2) as [Inf3 ->].
    { unfold sbools_of. autorewrite with cpodb. reflexivity. }
    induction n.
    - edestruct (S_of_DS_eq id _ Inf3) as [Inf4 ->].
      { simpl; autorewrite with cpodb; reflexivity. }
      rewrite <- const_DS_const; simpl.
      apply bools_ofs_empty.
    - edestruct (S_of_DS_eq id _ Inf3) as [Inf4 ->].
      { rewrite Fold_eq, lift_tl, lift_hd. reflexivity. }
      apply forall_nprod_inv in Hf as [], Inf1 as HH; destruct HH.
      edestruct (zip_map2 orb _ _ Inf4) as (Inf5 & Inf6 & ->).
      apply bools_ofs_cons; auto using bools_of_sbool_of, sbools_ofs_inf.
  Qed.

End BOOLS_OFS.


Section OLD_MASK.

  Import Streams.

  (* le masque comme il était avant *)
  CoFixpoint mask {A : Type} (absent: A) (k: nat) (rs: Stream bool) (xs: Stream A) : Stream A :=
    let mask' k' := mask absent k' (tl rs) (tl xs) in
    match k, hd rs with
    | 0, true    => Streams.const absent
    | 0, false   => hd xs  ⋅ mask' O
    | 1, true    => hd xs  ⋅ mask' O
    | S k', true => absent ⋅ mask' k'
    | S _, false => absent ⋅ mask' k
    end.
  Definition maskv := @mask svalue absent.

  Lemma mask'_abs :
    forall A (absent : A) k rs xs,
      O < k ->
      mask' absent O k rs xs ≡ const absent.
  Proof.
    cofix Cof; intros.
    destruct rs as [[]], xs; constructor; simpl; eauto.
    cases_eqn HH.
    apply Nat.eqb_eq in HH; subst; lia.
  Qed.

  (* on peut interchanger l'ancien et le nouveau *)
  Lemma mask_retro_compat :
    forall k rs xs,
      maskv k rs xs ≡ Str.maskv k rs xs.
  Proof.
    unfold maskv, Str.maskv, Str.mask.
    intros.
    match goal with |- _ ≡ ?aa => remember_st aa as v end.
    revert_all; cofix Cof; intros.
    rewrite (unfold_Stream (mask _ _ _ _)).
    rewrite (unfold_Stream (mask' _ _ _ _ _)) in Hv.
    destruct rs as [r rs], xs as [x xs].
    simpl in *.
    destruct r.
    - (* true *)
      cases_eqn HH; subst.
      + inv Hv; simpl in *; subst.
        constructor; simpl; auto.
        apply Cof.
        rewrite mask'_S in *; auto.
      + rewrite <- HH1, <- Hv, mask'_abs; auto.
        now constructor.
      + inv Hv; simpl in *; subst.
        constructor; simpl; auto.
        apply Cof.
        rewrite mask'_S in *; auto.
    - (* false *)
      inv Hv; simpl in *.
      destruct k as [|[]]; constructor; simpl; eauto.
  Qed.


  (* FIXME : ça vient d'une ancienne version de Vélus *)
  Lemma mask_nth {A} (absent: A) :
    forall n k rs xs,
      (mask absent k rs xs) # n = if (count rs) # n  =? k then xs # n else absent.
  Proof.
    unfold Str_nth.
    induction n, k as [|[|k]]; intros;
      unfold_Stv rs; simpl; auto.
    - pose proof (count_acc_grow 1 rs) as H.
      apply (ForAll_Str_nth_tl n) in H; inv H.
      assert (hd (Str_nth_tl n (count_acc 1 rs)) <> O) as E by lia.
      apply Nat.eqb_neq in E; rewrite E.
      pose proof (const_nth n absent); auto.
    - rewrite IHn; unfold count.
      destruct (hd (Str_nth_tl n (count_acc 1 rs)) =? 1) eqn: E;
        rewrite count_S_nth in E.
      + apply Nat.eqb_eq, eq_add_S, Nat.eqb_eq in E as ->; auto.
      + rewrite Nat.eqb_neq, Nat.succ_inj_wd_neg, <- Nat.eqb_neq in E;
          rewrite E; auto.
    - rewrite IHn; unfold count.
      destruct (hd (Str_nth_tl n (count_acc 1 rs)) =? S (S k)) eqn: E;
        rewrite count_S_nth in E.
      + apply Nat.eqb_eq, eq_add_S, Nat.eqb_eq in E; rewrite E; auto.
      + rewrite Nat.eqb_neq, Nat.succ_inj_wd_neg, <- Nat.eqb_neq in E;
          rewrite E; auto.
  Qed.

  (* FIXME : ça vient d'une ancienne version de Vélus *)
  Global Add Parametric Morphism {A} (absent: A) k : (mask absent k)
      with signature @EqSt _ ==> @EqSt _ ==> @EqSt _
        as mask_morph.
  Proof.
    intros rs rs' Ers xs xs' Exs.
    eapply ntheq_eqst; intros n.
    eapply eqst_ntheq with (n:=n) in Exs.
    rewrite 2 mask_nth, Exs, Ers. reflexivity.
  Qed.

  (* FIXME : ça vient d'une ancienne version de Vélus *)
  Global Add Parametric Morphism k : (maskv k)
      with signature @EqSt _ ==> @EqSt _ ==> @EqSt _
        as maskv_morph.
  Proof.
    intros rs rs' Ers xs xs' Exs.
    apply mask_morph; auto.
  Qed.

  Lemma Sapp_retro_compat :
    forall {PSyn Prefs} (G : @global PSyn Prefs),
    forall (H : history) (b : Stream bool) (f : ident) (es er : list exp) 
      (lann : list ann) (ss : list (list (Stream svalue))) (os : list (Stream svalue))
      (rs : list (list (Stream svalue))) (bs : Stream bool),
      Forall2 (sem_exp G H b) es ss ->
      Forall2 (sem_exp G H b) er rs ->
      bools_ofs (concat rs) bs ->
      (forall k : nat, sem_node G f (List.map (maskv k bs) (concat ss)) (List.map (maskv k bs) os)) ->
      sem_exp G H b (Eapp f es er lann) os.
  Proof.
    intros * ??? Hsem.
    econstructor; eauto.
    intro k.
    eapply sem_node_morph in Hsem; eauto.
    all: unfold EqSts; simpl_Forall; eauto using mask_retro_compat.
  Qed.

End OLD_MASK.




Lemma smask_maskv :
  forall k R U Ri Ui Mi,
    S_of_DSv (smask k R U) Mi ≡ maskv k (S_of_DS id R Ri) (S_of_DSv U Ui).
Proof.
  intros.
  remember_st (S_of_DSv (smask k R U) Mi) as sl.
  remember_st (maskv k (S_of_DS id R Ri) (S_of_DSv U Ui)) as sr.
  revert_all; cofix Cof; intros.
  remember_ds (smask k R U) as t.
  apply infinite_decomp in Ri as HH; destruct HH as (r & R' & Hr & ri').
  rewrite Hr, smask_eq in Ht.
  apply infinite_decomp in Ui as HH; destruct HH as (vx & s' & Hs' & si').
  edestruct (S_of_DS_eq id _ Ri _ Hr) as [Inf3 HH]; rewrite HH in Hsr; clear HH.
  edestruct (S_of_DSv_eq _ Ui _ Hs') as [Inf4 HH]; rewrite HH in Hsr; clear HH.
  cases.
  { (* DS_const abs *)
    rewrite <- Hsl, <- Hsr.
    rewrite DS_const_eq in Ht.
    edestruct (S_of_DSv_eq _ Mi _ Ht) as [Inf2 ->].
    unfold S_of_DSv; rewrite 2 S_of_DS_cons, unfold_Stream; simpl.
    constructor; simpl; auto.
    now rewrite <- const_DS_const.
  }
  all: rewrite <- ?Hs, ?Hs', ?APP_simpl, ?app_cons, ?rem_cons in Ht.
  all: edestruct (S_of_DSv_eq _ Mi _ Ht) as [Inf2 HH]; rewrite HH in Hsl; clear HH.
  all: unfold S_of_DSv in *; repeat rewrite S_of_DS_cons in *.
  all: constructor; [rewrite <- Hsl, <- Hsr; auto |]. (* hd ok, reste tl *)
  all: eapply Cof; rewrite <- ?Hsl, <- ?Hsr; simpl; [now apply _S_of_DS_eq|].
  all: apply maskv_morph; try reflexivity.
  Unshelve.
  all: eapply cons_infinite; now rewrite <- Ht.
Qed.

(* FIXME: l'énoncé est tordu mais ça fonctionne *)
Lemma map_mask_ :
  forall k rs Infr l (ss : nprod (length l)) InfI InfM,
    0 < length l ->
    NoDup l ->
    EqSts
      (map (maskv k (S_of_DS id rs Infr)) (Ss_of_nprod ss InfI))
      (Ss_of_nprod (np_of_env l (smask_env k rs (env_of_np l ss))) InfM).
Proof.
  intros * Hl Nd.
  erewrite Ss_map.
  2: intros; now apply symmetry, smask_maskv.
  apply _Ss_of_nprod_eq.
  destruct l as [|x l]; try (simpl in *; lia).
  apply nprod_eq; intros n d Hn.
  erewrite nth_lift; auto.
  rewrite (nth_np_of_env x d (x :: l)); auto.
  rewrite smask_env_proj_eq.
  erewrite env_of_np_nth; eauto 2 using mem_nth_nth.
  Unshelve.
  eapply forall_nprod_lift, forall_nprod_impl;
    eauto using smask_inf.
Qed.

Corollary map_mask :
  forall k rs Infr l (ss : nprod (length l)) InfI,
    0 < length l ->
    NoDup l ->
  exists InfM,
    EqSts
      (map (maskv k (S_of_DS id rs Infr)) (Ss_of_nprod ss InfI))
      (Ss_of_nprod (np_of_env l (smask_env k rs (env_of_np l ss))) InfM).
Proof.
  intros.
  unshelve (esplit; apply map_mask_); auto.
  (* FIXME : forall_np_of_env est trop faible en général ?? *)
  apply forall_np_of_env'; intros x Hin.
  rewrite smask_env_proj_eq.
  apply smask_inf, inf_dom_env_of_np; auto.
Qed.


(** Correspondance clocks_of/bss *)

Lemma ac_AC :
  forall s Inf,
    abstract_clock (S_of_DSv s Inf) ≡ S_of_DS id (AC s) (map_inf _ _ _ _ Inf).
Proof.
  clear.
  intros.
  match goal with
  | |- ?tt ≡ ?uu => remember_st tt as t; remember_st uu as u
  end.
  revert_all.
  cofix Cof; intros s Inf t Ht u Hu.
  destruct t, u.
  apply infinite_decomp in Inf as HH.
  destruct HH as (x & s' & Hs & Inf2).
  destruct (S_of_DSv_eq _ Inf _ Hs) as [Inf3 HH].
  rewrite HH in Ht; clear HH.
  setoid_rewrite S_of_DS_cons in Ht.
  edestruct (S_of_DS_eq id (AC s)) as [Inf4 HH]. { now rewrite Hs, AC_cons. }
  rewrite HH in Hu; clear HH.
  cases; rewrite S_of_DS_cons in Hu; inv Hu; inv Ht; simpl in *; subst.
  all: constructor; simpl; auto.
  all: eapply Cof; eauto; rewrite <- H0; eauto using _S_of_DS_eq.
Qed.

Lemma zip_zipWith :
  forall A B C (f : A -> B -> C),
    forall x y Infx Infy Infr,
      zipWith f (S_of_DS id x Infx) (S_of_DS id y Infy) ≡ S_of_DS id (ZIP f x y) Infr.
Proof.
  clear.
  intros.
  remember_st (S_of_DS id x Infx) as xs.
  remember_st (S_of_DS id y Infy) as ys.
  remember_st (S_of_DS id _ Infr) as rs.
  revert_all; cofix Cof; intros.
  destruct xs as [vx xs], ys as [vy ys], rs as [vr rs].
  apply S_of_DS_Cons in Hxs as (vx' & xs' & Hx & Hvx & Infx' & Hxs).
  apply S_of_DS_Cons in Hys as (vy' & ys' & Hy & Hvy & Infy' & Hys).
  apply S_of_DS_Cons in Hrs as (vr' & rs' & Hr & Hvr & Infr' & Hrs).
  rewrite Hx, Hy, zip_cons in Hr.
  apply Con_eq_simpl in Hr as [].
  constructor; simpl.
  - subst; auto.
  - unshelve eapply Cof; eauto.
    { eapply infinite_morph; eauto. }
    rewrite <- Hrs.
    now apply _S_of_DS_eq.
Qed.

Lemma _clocks_of_bss :
  forall env l Inf Infb,
    NoDup l ->
    clocks_of (Ss_of_nprod (np_of_env l env) Inf)
      ≡ S_of_DS id (bss l env) Infb.
Proof.
  clear.
  induction l as [| x [| y l]]; intros * ND.
  - rewrite clocks_of_nil.
    unshelve rewrite (const_DS_const id false); auto.
    apply _S_of_DS_eq; auto.
  - simpl.
    rewrite clocks_of_ac, ac_AC.
    now apply _S_of_DS_eq.
  - inv ND.
    setoid_rewrite clocks_of_cons.
    setoid_rewrite IHl; auto.
    rewrite ac_AC, zip_zipWith.
    apply _S_of_DS_eq; auto.
  Unshelve.
  rewrite bss_cons in Infb; apply inf_zip in Infb as [].
  all: auto.
Qed.

Lemma bss_env_inf :
  forall l env,
    (forall_nprod (@infinite _) (np_of_env l env)) ->
    infinite (bss l env).
Proof.
  induction l; intros * Hinf.
  - apply DS_const_inf.
  - rewrite bss_cons.
    apply forall_nprod_inv in Hinf as [Infh Inft].
    setoid_rewrite nprod_hd_cons in Infh.
    apply zip_inf.
    + apply map_inf, Infh.
    + (* ça fait quand même chier de devoir détruire l ici *)
      apply IHl; destruct l; auto.
Qed.

Corollary clocks_of_bss :
  forall env l Inf,
    NoDup l ->
    exists Infb,
    clocks_of (Ss_of_nprod (np_of_env l env) Inf) ≡
      S_of_DS id (bss l env) Infb.
Proof.
  intros.
  pose (Infb := bss_env_inf _ _ Inf).
  exists Infb.
  rewrite (_clocks_of_bss _ _ _ Infb); auto.
  now apply _S_of_DS_eq.
Qed.


Section Inf_Dom.

Definition inf_dom Γ ins envI env :=
  forall x, IsVar Γ x -> infinite (denot_var ins envI env x).

Global Add Parametric Morphism Γ ins : (inf_dom Γ ins)
       with signature @Oeq (DS_prod SI) ==> @Oeq (DS_prod SI) ==> iff
         as inf_dom_morph.
Proof.
  unfold inf_dom.
  intros ?? Eq1 ?? Eq2.
  setoid_rewrite Eq1.
  setoid_rewrite Eq2.
  tauto.
Qed.

(* FIXME: pourquoi on en a besoin ??
c'est juste une spécialisation de inf_dom_morph ???? *)
Global Add Parametric Morphism Γ ins envI : (inf_dom Γ ins envI)
       with signature @Oeq (DS_prod SI) ==> iff
         as inf_dom_morph2.
Proof.
  split; intros Hinf; eapply inf_dom_morph in Hinf; eauto.
Qed.

Lemma infinite_dom_app_l :
  forall (env : DS_prod SI) l1 l2,
    infinite_dom env (l1 ++ l2) ->
    infinite_dom env l1.
Proof.
  unfold infinite_dom.
  setoid_rewrite in_app_iff.
  intros * H ??; apply H; tauto.
Qed.

Lemma infinite_dom_np :
  forall env l,
    forall_nprod (@infinite _) (np_of_env l env) ->
    infinite_dom env l.
Proof.
  unfold infinite_dom.
  induction l; intros Hf x Hin; inv Hin;
    apply forall_nprod_inv in Hf as [Inf1 Inf2]; simpl in *.
  - now setoid_rewrite nprod_hd_cons in Inf1.
  - apply IHl; auto.
    destruct l; auto.
Qed.

Lemma inf_dom_decomp :
  forall Γ ins outs envI env,
    infinite_dom envI ins ->
    infinite_dom env outs ->
    map fst Γ = ins ++ outs ->
    inf_dom Γ ins envI env.
Proof.
  unfold infinite_dom, inf_dom, denot_var.
  intros * Hi Ho Heq x Isv%IsVar_In.
  rewrite Heq, in_app_iff in Isv.
  cases_eqn Hmem.
  - apply mem_ident_spec in Hmem; auto.
  - apply mem_ident_false in Hmem.
    destruct Isv; [ contradiction | auto ].
Qed.

End Inf_Dom.


(** ** Fonctions pour passer d'un [DS_prod SI] à un Str.history *)

Lemma IsVar_dec : forall Γ x, { IsVar Γ x } + { ~ IsVar Γ x }.
Proof.
  intros.
  destruct (ListDec.In_dec ident_eq_dec x (map fst Γ)) as [|HH].
  - left; now apply IsVar_fst.
  - right; contradict HH; now apply IsVar_fst.
Qed.


Definition hist_of_envs Γ ins envI env (InfΓ : inf_dom Γ ins envI env) : history :=
  fun lx => match lx with
         | Var x => match IsVar_dec Γ x with
                   | left isv => Some (S_of_DSv (denot_var ins envI env x) (InfΓ x isv))
                   | _ => None
                   end
         | _ => None
         end.

Lemma sem_hist_of_envs :
  forall Γ ins envI env InfΓ x Infx,
    IsVar Γ x ->
    sem_var (hist_of_envs Γ ins envI env InfΓ) (Var x)
      (S_of_DSv (denot_var ins envI env x) Infx).
Proof.
  intros.
  unfold hist_of_envs.
  destruct (IsVar_dec Γ x) eqn:Hdec; [| contradiction].
  econstructor.
  rewrite Hdec; reflexivity.
  now apply _S_of_DS_eq.
Qed.

Lemma sem_var_nins : forall Γ ins envI env InfΓ x s Inf,
    IsVar Γ x ->
    ~ In x ins ->
    s == env x ->
    sem_var (hist_of_envs Γ ins envI env InfΓ) (Var x) (S_of_DSv s Inf).
Proof.
  intros * Hvar Hnin Heq.
  unshelve eapply sem_var_EqSt, sem_hist_of_envs;
    try reflexivity; auto.
  apply _S_of_DS_eq.
  unfold denot_var; cases_eqn Hmem.
  apply mem_ident_spec in Hmem; contradiction.
Qed.

Lemma sem_hist_of_envs' :
  forall Γ ins envI env InfΓ x s Inf,
    IsVar Γ x ->
    s == denot_var ins envI env x ->
    sem_var (hist_of_envs Γ ins envI env InfΓ) (Var x) (S_of_DSv s Inf).
Proof.
  intros.
  unfold hist_of_envs.
  destruct (IsVar_dec Γ x) eqn:Hdec; [| contradiction].
  econstructor.
  rewrite Hdec; reflexivity.
  now apply _S_of_DS_eq.
Qed.

Lemma sem_var_ins : forall Γ ins envI env InfΓ x s Inf,
    IsVar Γ x ->
    In x ins ->
    s == envI x ->
    sem_var (hist_of_envs Γ ins envI env InfΓ) (Var x) (S_of_DSv s Inf).
Proof.
  clear.
  intros * Isv Hin Heq.
  apply sem_hist_of_envs'; auto.
  unfold denot_var; cases_eqn Hmem.
  apply mem_ident_false in Hmem; contradiction.
Qed.



(** Hypothèse sur les entrées d'un nœud : elles doivent être bien typées
    et respecter leurs annotations d'horloge. *)
Definition wf_ins {PSyn Prefs} (n : @node PSyn Prefs) envI bs :=
  let ins := List.map fst n.(n_in) in
  let Γ := senv_of_ins (n_in n) ++ senv_of_decls (n_out n) in
  wf_env Γ ins envI bs 0.


Section Ok_node.

Context {PSyn : list decl -> block -> Prop}.
Context {Prefs : PS.t}.

Variables
  (G : @global PSyn Prefs)
  (envG : Dprodi FI).

(** Toutes les hypothèses de section sur G et envG seront obtenues par
    récurrence dans ok_global. *)

Hypothesis (Wtg : wt_global G).
Hypothesis (Wcg : wc_global G).
Hypothesis (Hrg : restr_global G).

Hypothesis InfG :
  forall f nd envI,
    find_node f G = Some nd ->
    infinite_dom envI (List.map fst (n_in nd)) ->
    infinite_dom (envG f envI) (List.map fst (n_out nd)).

Hypothesis AbsG :
  forall f X,
    (* remarque: on pourrait avoir une égalité avec inf_dom *)
    envG f (APP_env abs_env X) <= APP_env abs_env (envG f X).

Hypothesis Hlp :
  (* forall f X Y n, *)
  (*   take_env n X == take_env n Y -> *)
  (*   take_env n (envG f X) == take_env n (envG f Y). *)
  forall f X n,
    envG f (take_env n X) == take_env n (envG f X).

Hypothesis Wfg :
  forall f n envI,
    find_node f G = Some n ->
    let ins := List.map fst n.(n_in) in
    let Γ := senv_of_ins (n_in n) ++ senv_of_decls (n_out n) ++ get_locals (n_block n) in
    forall bs, bss ins envI <= bs ->
          (* no_rte_node G ins envG envI (envG f envI) n -> *)
          wf_env Γ ins envI bs 0 ->
          wf_env Γ ins envI bs (envG f envI).

Hypothesis Halign :
  forall f n,
    find_node f G = Some n ->
    let ins := List.map fst (n_in n) in
    let Γ := senv_of_ins (n_in n) ++ senv_of_decls (n_out n) ++ get_locals (n_block n) in
    forall envI,
    wf_env Γ ins envI (bss ins envI) (envG f envI) ->
    abs_alignLE envI (envG f envI).

Hypothesis Hnode :
  forall f n envI,
    find_node f G = Some n ->
    let ins := List.map fst (n_in n) in
    let outs := List.map fst (n_out n) in
    let xs := np_of_env ins envI in
    let os := np_of_env outs (envG f envI) in
    wf_ins n envI (bss ins envI) ->
    (* all_infinite envI -> *)
    (* on peut obtenir Infi et Info comme suit :
       set (Infi := forall_np_of_env _ _ _ infI)
       set (Info := forall_np_of_env _ _ _ (InfG _ _ infI)) *)
    forall Infi Info,
    sem_node G f (Ss_of_nprod xs Infi) (Ss_of_nprod os Info).

(* Hypothesis Hnorte : *)
(*   forall f n envI, *)
(*     find_node f G = Some n -> *)
(*     let ins := List.map fst (n_in n) in *)
(*     no_rte_node G ins envG envI (envG f envI) n. *)


(** On le laisse ici car il dépend des hypothèses de section *)
Lemma ok_reset :
  forall f n,
    find_node f G = Some n ->
    let nf := envG f in
    let nin := List.map fst (n_in n) in
    let nout := List.map fst (n_out n) in
    forall rs (ss : nprod (length nin)),
    let os := np_of_env nout (sreset nf rs (env_of_np nin ss)) in
    wf_ins n (env_of_np nin ss) (bss nin (env_of_np nin ss)) ->
    forall InfI InfO Infr,
    forall k, sem_node G f (List.map (maskv k (S_of_DS id rs Infr)) (Ss_of_nprod ss InfI))
                      (List.map (maskv k (S_of_DS id rs Infr)) (Ss_of_nprod os InfO)).
Proof.
  intros * Hfind * Hwf *.
  pose proof (n_nodup n) as [Ndio _].
  apply NoDup_app_l in Ndio as Ndi.
  apply NoDup_app_r in Ndio as Ndo.
  pose proof (n_ingt0 n) as Innil; rewrite <- (map_length fst) in Innil.
  pose proof (n_outgt0 n) as Onnil; setoid_rewrite <- (map_length fst) in Onnil.
  apply wc_find_node in Hfind as HH; auto; destruct HH as (G' & Wcn).
  edestruct map_mask as [Inf3 ->]; auto.
  edestruct map_mask as [Inf4 ->]; auto.
  (* on prépare wf_ins pour la suite *)
  apply (wf_env_smask0 _ _ _ _ k rs) in Hwf as Hwf; eauto using clock_ins_stable.
  rewrite <- bss_smask in Hwf; auto.
  eapply sem_node_morph with (x := f), Hnode with (n := n); eauto.
  - (* input ok *)
    reflexivity.
  - (* output *)
    subst os nf.
    fold nout in Onnil, Ndo |- *.
    apply _Ss_of_nprod_eq, np_of_env_ext.
    intros i Ini.
    rewrite (smask_sreset' (envG f)); eauto 2 using inf_dom_env_of_np.
    rewrite 2 smask_env_proj_eq, env_of_np_of_env_proj; auto.
    eapply Halign, Wfg; eauto.
    apply wf_env_0_ext; auto.
    Unshelve.
    apply forall_np_of_env'; intros.
    eapply InfG; eauto using smask_env_inf, inf_dom_env_of_np.
Qed.


(** Deux tactiques bien pratiques pour la suite *)

(* C'est souvent une bonne idée de généraliser les termes [infinite_exp]
   car ça élimine une dépendance sur [denot_exp]. *)
Ltac gen_infinite_exp :=
  repeat (
  simpl; (* important, même si l'action n'est pas visible *)
  let f := fresh "Inf" in
  match goal with
  | |- context [ infinite_exp ?H1 ?H2 ?H3 ?H4 ?H5 ?H6 ?H7 ?H8 ?H9 ?H10 ?H11 ?H12 ] =>
      generalize (infinite_exp H1 H2 H3 H4 H5 H6 H7 H8 H9 H10 H11 H12) as f
  | |- context [ infinite_exps ?H1 ?H2 ?H3 ?H4 ?H5 ?H6 ?H7 ?H8 ?H9 ?H10 ?H11 ?H12 ?H13 ] =>
      generalize (infinite_exps H1 H2 H3 H4 H5 H6 H7 H8 H9 H10 H11 H12 H13) as f
  | |- context [ infinite_expss ?H1 ?H2 ?H3 ?H4 ?H5 ?H6 ?H7 ?H8 ?H9 ?H10 ?H11 ?H12 ?H13 ?H14 ?H15 ?H16 ] =>
      generalize (infinite_expss H1 H2 H3 H4 H5 H6 H7 H8 H9 H10 H11 H12 H13 H14 H15 H16) as f
  end).

(* Isole un terme [denot_exp ...] dans une égalisé [Hse] afin de pouvoir
   réécrire [denot_exp_eq] dedans, sans complications liées à S_of_DSv. *)
Ltac save_denot_exp se Hse :=
  gen_infinite_exp;
  simpl; (* important, même si l'action n'est pas visible *)
  match goal with
  | |- context [ ?f1 (?f2 (?f3 (denot_exp ?e1 ?e2 ?e3) ?e4) ?e5) ?e6 ] =>
      remember (f1 (f2 (f3 (denot_exp e1 e2 e3) e4) e5) e6)
      as se eqn:Hse
  end.

(* Une fois [denot_exp_eq] appliqué, on voit souvent apparaître [denot_exps]
   sur les sous-expressions. Si l'hypothèse de récurrence est déjà dégrossie,
   il peut être utile d'abstraire les sous-flots avec ça : *)
Ltac gen_inf_sub_exps :=
  gen_infinite_exp;
  gen_sub_exps. (* voir dans Denot.v *)


(* FIXME: ce morphime est un cas particulier
   de maskv_morph et pourtant il faut le déclarer
   pour que les réécritures fonctionnent dans ok_sem_Eapp
 *)
Global Add Parametric Morphism k bs : (maskv k bs)
    with signature @EqSt _ ==> @EqSt _
      as maskv_morph2.
Proof.
  now apply maskv_morph.
Qed.


(* À partir de [sem_exp (denot_exp ...)], typiquement obtenu par hypothèse
   d'induction, on construit du [sem_exp (denot_exps ...)]. *)
Lemma sem_sub_exps :
  forall {PSyn Prefs} (G : @global PSyn Prefs),
  forall ins H envI envG bs bsi env,
  forall (es : list exp) Infes,
    Forall (fun e => forall Infe, sem_exp G H (S_of_DS id bs bsi) e
                    (Ss_of_nprod (denot_exp G ins e envG envI env) Infe)) es ->
    exists sss,
      EqSts (concat sss) (Ss_of_nprod (denot_exps G ins es envG envI env) Infes)
      /\ Forall2 (sem_exp G H (S_of_DS id bs bsi)) es sss.
Proof.
  clear.
  induction es as [| e1 es]; intros * Hsem.
  - exists []; split; now auto.
  - edestruct (Ss_of_nprod_eq _ Infes) as [Inf1 Eq1].
    { rewrite denot_exps_eq. reflexivity. }
    edestruct (Ss_app _ _ Inf1) as (Inf2 & Inf3 & Eq2).
    setoid_rewrite Eq1.
    setoid_rewrite Eq2.
    clear Eq1 Eq2.
    inv Hsem.
    destruct (IHes Inf3) as (sss & Heq & Hsem); auto.
    eexists (_ :: sss); split; unshelve eauto; auto.
    apply Forall2_app; auto.
    now apply _Ss_of_nprod_eq.
Qed.

(* À partir de [sem_exp (denot_exp ...)], typiquement obtenu par hypothèse
   d'induction, on construit du [sem_exp (denot_expss ...)]. *)
Lemma sem_sub_expss :
  forall {PSyn Prefs} (G : @global PSyn Prefs),
  forall ins H envI envG bs bsi env,
  forall (ess : list (enumtag * list exp)) n Infes,
    Forall (fun es => length (annots (snd es)) = n) ess ->
    Forall (Forall (fun e => forall Infe, sem_exp G H (S_of_DS id bs bsi) e
                            (Ss_of_nprod (denot_exp G ins e envG envI env) Infe)))
      (map snd ess) ->
    Forall2 (fun '(_, es) ss => exists sss,
                 EqSts ss (concat sss)
                 /\ Forall2 (sem_exp G H (S_of_DS id bs bsi)) es sss)
      ess (Ss_of_nprods (denot_expss G ins ess n envG envI env) Infes).
Proof.
  clear.
  intros *.
  induction ess as [|[t es] ess]; intros * Hl Hsem; inv Hl; inv Hsem. now simpl.
  constructor.
  - (* es *)
    destruct (Nat.eq_dec (list_sum (map numstreams es)) (length (annots es)))
      as [Heq|Hneq] eqn:Hdec.
    2: clear Hdec; rewrite annots_numstreams in Hneq; congruence.
    remember (forall_nprod_hd _ _ _) as Inf1 eqn:HH; clear HH.
    assert (Inf : forall_nprod (@infinite _) (denot_exps G ins es envG envI env0)).
    { simpl (snd _) in *.
      rewrite denot_expss_eq, Hdec in Infes.
      apply (@app_forall_nprod _ _ 1) in Infes as [Inf].
      unfold eq_rect in Inf; cases. }
    take (Forall _ es) and unshelve eapply sem_sub_exps in it as (sss & Hsss & Hsem); auto.
    exists sss; split; auto.
    rewrite Hsss.
    edestruct (Ss_of_nprod_eq _ Inf1) as [Inf2 ->].
    { simpl (snd _).
      rewrite denot_expss_eq, Hdec, nprod_hd_cons.
      reflexivity. }
    clear; revert Inf2 Inf.
    gen_sub_exps.
    rewrite Heq; auto using _Ss_of_nprod_eq.
  - (* tail *)
    destruct ess as [|es2 ess]; auto.
    eapply (Forall2_morph _ _ _ _ EqSts) in IHess; eauto.
    + (* morphisme à la con *)
      clear; intros [] [] HH x ?? (?&?&?); inv HH.
      esplit; split; eauto; now transitivity x.
    + constructor; [apply _Ss_of_nprod_eq | apply _Ss_of_nprods_eq].
      Unshelve.
      all: repeat rewrite denot_expss_eq in *; cases.
      all: contradict n; simpl; now rewrite annots_numstreams.
Qed.


(** On traite à part le cas des appels de nœuds car il apparaît à la fois
    dans une expression Eapp et dans une équation de type xs=[Eapp].
    Dand les deux cas seules les hypothèses du lemme suivant sont
    nécessaires. En particulier, rien à dire sur la dépendance entre les
    horloges de l'équation et de l'application. *)
Lemma ok_sem_Eapp :
  forall Γ ins env envI,
    let bs := bss ins envI in
    forall bsi (InfΓ : inf_dom Γ ins envI env),
    wf_env Γ ins envI bs env ->
    let H := hist_of_envs Γ ins envI env InfΓ in
    forall f n es er anns bck sub,
      Forall2 (fun (et : type) '(_, (t, _, _)) => et = t) (typesof es) (n_in n) ->
      Forall2 (WellInstantiated bck sub) (List.map (fun '(x, (_, ck, _)) => (x, ck)) (n_in n)) (nclocksof es) ->
      Forall (fun e : exp => numstreams e = 1) er ->
      wc_env (map (fun '(x, (_, ck, _)) => (x, ck)) n.(n_in)) ->
      find_node f G = Some n ->
      length (anns) = length (n_out n) ->
      Forall restr_exp es ->
      Forall (wt_exp G Γ) es ->
      Forall (wc_exp G Γ) es ->
      Forall (no_rte_exp G ins envG envI env) es ->
      Forall (fun e => forall Infe,
                  sem_exp G H (S_of_DS id bs bsi) e
                    (Ss_of_nprod (denot_exp G ins e envG envI env) Infe)) es ->
      Forall restr_exp er ->
      Forall (wt_exp G Γ) er ->
      Forall (fun e => typeof e = [bool_velus_type]) er ->
      Forall (wc_exp G Γ) er ->
      Forall (no_rte_exp G ins envG envI env) er ->
      Forall (fun e => forall Infe,
                  sem_exp G H (S_of_DS id bs bsi) e
                    (Ss_of_nprod (denot_exp G ins e envG envI env) Infe)) er ->
      let os := denot_exp G ins (Eapp f es er anns) envG envI env in
      forall infO,
        sem_exp G H (S_of_DS id bs bsi) (Eapp f es er anns) (Ss_of_nprod os infO).
Proof.
  intros ?? env * Hc * WTi WIi Nr1 WCi Hfind Hlo Hr Hwt Hwc Hoc Hsem Hrr Hwtr Hwtr' Hwcr Hocr Hsemr ??.
  apply Forall2_length in WTi as Hli.
  rewrite length_typesof_annots in Hli.
  apply (Forall_impl _ (wt_exp_wx_exp G Γ)) in Hwt as Hwx, Hwtr as Hwxr.
  apply (Forall_impl _ (wt_exp_wl_exp G Γ)) in Hwt as Hwl, Hwtr as Hwlr.
  set (ss := denot_exps G ins es envG envI env).
  set (rs := denot_exps G ins er envG envI env).
  (* utile pour après ou pas ? *)
  assert (Hins : wf_ins n (env_of_np (idents (n_in n)) ss)
                   (bss (idents (n_in n)) (env_of_np (idents (n_in n)) ss))).
  { unfold wf_ins.
    rewrite annots_numstreams in Hli.
    pose proof (nclocksof_sem G envG ins envI env es) as Ncs.
    edestruct @safe_exps_ with (es := es) as (sTy & sCl & sEf);
      eauto using wf_env_loc, wf_env_0_ext.
    rewrite clocksof_nclocksof in sCl.
    eapply safe_inst_in with (ss := ss) in Hli as Hec; eauto.
    eapply wf_env_morph in Hec; eauto 1.
    (* équivalence des horloges *)
    apply wf_env_decompose in Hec as (?& Hcl &?).
    apply bss_le_bs in Hcl as Hbs; auto.
    apply infinite_le_eq in Hbs as ->; auto.
    eapply bss_inf_dom, inf_dom_env_of_np, infinite_exps; eauto.
  }
  edestruct @sem_sub_exps with (es := es) as (sss & Heqs & Hsss); eauto.
  edestruct @sem_sub_exps with (es := er) as (rss & Heqr & Hrss); eauto.
  clear Hsem Hsemr.
  Unshelve.
  2,3: now eauto using infinite_exps.
  eapply Sapp_retro_compat; eauto.
  - (* bools_ofs *)
    rewrite Heqr.
    eapply safe_exps_ in Hwtr as (rTy & _ & _);
      eauto using wf_env_loc, wf_env_0_ext.
    apply typeof_same, Forall2_Forall_eq with (2:= rTy), Forall_forall_nprod in Hwtr'.
    unshelve apply bools_ofs_sbools_of;
      eauto using sbools_ofs_inf, infinite_exp, infinite_exps.
  - (* sem_node *)
    intro k.
    rewrite Heqs.
    subst ss rs; revert infO Hins; revert os.
    save_denot_exp se Hse.
    setoid_rewrite denot_exp_eq in Hse; revert Hse; simpl.
    gen_sub_exps.
    rewrite Hfind, <- annots_numstreams, Hli.
    unfold decl in Hlo; rewrite <- (map_length fst) in Hlo.
    rewrite <- (map_length fst).
    unfold idents, eq_rect.
    cases; intros; subst; try congruence.
    apply ok_reset; auto.
Qed.


(** Morphismes rencontrés dans la preuve de [ok_sem_exp].
    La plupart sont ad hoc, donc on les laisse ici. *)

Local Instance : forall k t,
    Proper ((@EqSt _) ==> (@EqSt _) ==> Basics.impl)
      (fun s => when k s t).
Proof.
  intros.
  solve_proper.
Qed.

Local Instance : forall s l,
    Proper (EqSts ==> EqSt (A:=svalue) ==> Basics.impl)
      (fun ss => merge s (combine l ss)).
Proof.
  intros.
  unfold EqSts.
  solve_proper.
Qed.

Local Instance : forall s l,
    Proper (EqSts ==> EqSt (A:=svalue) ==> Basics.impl)
      (fun ss : list (Stream svalue) => case s (combine l ss) None).
Proof.
  intros.
  unfold EqSts.
  solve_proper.
Qed.

Local Instance : forall s l,
    Proper (EqSts ==> (EqSt (A:=svalue) * EqSt (A:=svalue)) ==> Basics.impl)
      (fun ss dos => case s (combine l ss) (Some (fst dos)) (snd dos)).
Proof.
  intros.
  unfold EqSts.
  solve_proper.
Qed.

Local Instance : forall s l d,
    Proper (EqSts ==> EqSt (A:=svalue) ==> Basics.impl)
      (fun ss b => case s (combine l (tl ss)) (Some (hd d ss)) b).
Proof.
  intros.
  unfold EqSts.
  solve_proper.
Qed.

Lemma ty_DS_wt_stream :
  forall ty s si,
    ty_DS ty s ->
    wt_stream (S_of_DSv s si) ty.
Proof.
  clear.
  unfold ty_DS.
  intros * Hty.
  remember_st (S_of_DSv s si) as t.
  revert_all; cofix Cof; intros.
  destruct t.
  apply S_of_DS_Cons in Ht as (?&?& Hs &?&?&?).
  rewrite Hs in *.
  inv Hty.
  constructor.
  - cases.
  - eapply Cof; eauto.
Qed.


(** On redéfinit [Safe.safe_exp], qui a une hypothèse de [wf_env] un peu
    différente que [Wfg] présente dans cette section : son Γ n'inclut
    pas [get_locals (n_block n)].
 *)
Lemma safe_exp :
  forall Γ ins envI bs env,
    wf_env Γ ins envI bs env ->
    bss ins envI <= bs ->
    forall (e : exp),
      restr_exp e ->
      wt_exp G Γ e ->
      wc_exp G Γ e ->
      no_rte_exp G ins envG envI env e ->
      let ss := denot_exp G ins e envG envI env in
      forall_nprod safe_DS ss.
Proof.
  intros.
  eapply safe_exp; eauto using wf_env_0_ext, wf_env_loc.
Qed.

Lemma ok_sem_exp :
  forall Γ ins env envI InfΓ,
    let bs := bss ins envI in
    forall bsi,
    wf_env Γ ins envI bs env ->
    (* let H := hist_of_envs ins envI InfI env Inf in *)
    let H := hist_of_envs Γ ins envI env InfΓ in
    forall (e : exp) (Hwt : wt_exp G Γ e) (Hwc : wc_exp G Γ e) (Hr : restr_exp e),
      no_rte_exp G ins envG envI env e ->
      let ss := denot_exp G ins e envG envI env in
      forall Infe,
      (* let Infe := infinite_exp _ _ _ _ _ _ InfG bsi InfI Inf _ in *)
      sem_exp G H (S_of_DS id bs bsi) e (Ss_of_nprod ss Infe).
Proof.
  intros ?? env * Hc H.
  induction e using exp_ind2; intros * ??? Hoc ss Infe.
  all: inv Hr; subst ss; simpl.
  - (* Econst *)
    constructor.
    edestruct S_of_DSv_eq as [Infe' ->].
    { setoid_rewrite denot_exp_eq. reflexivity. }
    unshelve rewrite <- ok_const; auto using sconst_inf, DS_of_S_inf.
    apply _S_of_DS_eq.
    now rewrite DS_of_S_of_DS.
  - (* Eenum *)
    constructor.
    edestruct S_of_DSv_eq as [Infe' ->].
    { setoid_rewrite denot_exp_eq. reflexivity. }
    unshelve rewrite <- ok_enum; auto using sconst_inf, DS_of_S_inf.
    apply _S_of_DS_eq.
    now rewrite DS_of_S_of_DS.
  - (* Evar *)
    constructor.
    apply wt_exp_wx_exp in Hwt; inv Hwt.
    edestruct S_of_DSv_eq as [Infe' ->].
    { setoid_rewrite denot_exp_eq. reflexivity. }
    apply sem_hist_of_envs; auto.
  - (* Eunop *)
    eapply safe_exp in Hoc as Hs; eauto using restr_exp.
    apply wt_exp_wl_exp in Hwt as Hwl.
    inv Hwt. inv Hwc. inv Hoc. inv Hwl.
    edestruct (Ss_of_nprod_eq _ Infe) as [Hinf0 HH].
    { setoid_rewrite denot_exp_eq. reflexivity. }
    rewrite HH; clear HH.
    rewrite denot_exp_eq in Hs.
    revert Hinf0 IHe Hs; simpl.
    gen_inf_sub_exps.
    take (numstreams e = 1) and rewrite it.
    take (typeof e = _) and rewrite it.
    econstructor; eauto.
    eapply IHe; eauto.
    apply ok_unop; auto.
    Unshelve.
    unfold sunop in Hinf0; now apply inf_map in Hinf0.
  - (* Ebinop *)
    eapply safe_exp in Hoc as Hs; eauto using restr_exp.
    apply wt_exp_wl_exp in Hwt as Hwl.
    inv Hwt. inv Hwc. inv Hoc. inv Hwl.
    edestruct (Ss_of_nprod_eq _ Infe) as [Hinf0 HH].
    { setoid_rewrite denot_exp_eq. reflexivity. }
    rewrite HH; clear HH.
    rewrite denot_exp_eq in Hs.
    revert Hinf0 IHe1 IHe2 Hs; simpl.
    gen_inf_sub_exps.
    take (numstreams e1 = 1) and rewrite it.
    take (numstreams e2 = 1) and rewrite it.
    take (typeof e1 = _) and rewrite it.
    take (typeof e2 = _) and rewrite it.
    econstructor; eauto.
    eapply IHe1; eauto.
    eapply IHe2; eauto.
    apply ok_binop; auto.
    Unshelve.
    all: now apply inf_sbinop in Hinf0 as [].
  - (* Efby *)
    eapply safe_exp in Hoc as Hs; eauto using restr_exp.
    apply wt_exp_wl_exp in Hwt as Hwl.
    apply wt_exp_wx_exp in Hwt as Hwx.
    inv Hwt. inv Hwc. inv Hoc. inv Hwl. inv Hwx.
    apply Forall_impl_inside with (P := wt_exp _ _) in H0, H1; auto.
    apply Forall_impl_inside with (P := wc_exp _ _) in H0, H1; auto.
    apply Forall_impl_inside with (P := restr_exp) in H0, H1; auto.
    apply Forall_impl_inside with (P := no_rte_exp _ _ _ _ _) in H0, H1; auto.
    unshelve eapply sem_sub_exps in H0 as (s0ss & Eq0 & Sem0), H1 as (sss & Eq1 & Sem);
      eauto using infinite_exps.
    econstructor; eauto.
    rewrite Eq0, Eq1.
    revert Infe Hs.
    save_denot_exp se Hse.
    setoid_rewrite denot_exp_eq in Hse; revert Hse; simpl.
    gen_sub_exps.
    rewrite annots_numstreams in *.
    unfold eq_rect; cases; intros; subst; try congruence.
    clear - Hs.
    induction (list_sum (map numstreams es)); constructor.
    * edestruct (S_of_DSv_eq) as [Inf3 HH]. 2: setoid_rewrite HH at 3.
      { rewrite lift2_hd. reflexivity. }
      apply forall_nprod_hd in Hs.
      rewrite lift2_hd in Hs.
      apply ok_fby; auto.
    * edestruct (@Ss_of_nprod_eq n) as [Inf3 HH]. 2: setoid_rewrite HH at 3.
      { rewrite lift2_tl. reflexivity. }
      apply forall_nprod_tl in Hs.
      rewrite lift2_tl in Hs.
      eapply IHn; eauto using forall_nprod_tl.
  - (* Ewhen *)
    destruct x as [x ty].
    eapply safe_exp in Hoc as Hs; eauto using restr_exp.
    apply wt_exp_wl_exp in Hwt as Hwl.
    apply wt_exp_wx_exp in Hwt as Hwx.
    inv Hwt. inv Hwc. inv Hoc. inv Hwl. inv Hwx.
    apply Forall_impl_inside with (P := wt_exp _ _) in H0; auto.
    apply Forall_impl_inside with (P := wc_exp _ _) in H0; auto.
    apply Forall_impl_inside with (P := restr_exp) in H0; auto.
    apply Forall_impl_inside with (P := no_rte_exp _ _ _ _ _) in H0; auto.
    unshelve eapply sem_sub_exps in H0 as (s0ss & Eq0 & Sem0);
      eauto using infinite_exps.
    econstructor; simpl; eauto.
    + unshelve apply sem_hist_of_envs; auto using denot_var_inf.
    + rewrite Eq0.
      revert Infe Hs.
      save_denot_exp se Hse.
      setoid_rewrite denot_exp_eq in Hse; revert Hse; simpl.
      gen_inf_sub_exps.
      rewrite annots_numstreams in *.
      unfold eq_rect; cases; intros; subst; try congruence.
      clear - Hs.
      induction (list_sum (map numstreams es)); constructor.
      * edestruct (S_of_DSv_eq) as [Inf3 HH]. 2: setoid_rewrite HH at 3.
        { rewrite llift_hd. reflexivity. }
        apply forall_nprod_hd in Hs.
        rewrite llift_hd in Hs.
        apply ok_when; auto.
      * edestruct (@Ss_of_nprod_eq n) as [Inf3 HH]. 2: setoid_rewrite HH at 2.
        { rewrite llift_tl. reflexivity. }
        apply forall_nprod_tl in Hs.
        rewrite llift_tl in Hs.
        eapply IHn; eauto.
  - (* Merge *)
    destruct x as [x ty].
    eapply safe_exp in Hoc as Hs; eauto using restr_exp.
    apply wt_exp_wl_exp in Hwt as Hwl.
    apply wt_exp_wx_exp in Hwt as Hwx.
    inv Hwt. inv Hwc. inv Hoc.
    rewrite <- Forall_map, <- Forall_concat in *.
    inv Hwl. inv Hwx.
    apply Forall_impl_inside with (P := wt_exp _ _) in H0; auto.
    apply Forall_impl_inside with (P := wc_exp _ _) in H0; auto.
    take (Forall restr_exp _) and rewrite map_map in it.
    apply Forall_impl_inside with (P := restr_exp) in H0; auto.
    apply Forall_concat in it.
    apply Forall_impl_inside with (P := no_rte_exp _ _ _ _ _) in H0; auto.
    unshelve eapply Forall_concat, sem_sub_expss in H0; eauto using infinite_expss.
    eapply Smerge_alt2 with (d:= (Streams.const absent)) in H0; simpl; eauto.
    + unshelve apply sem_hist_of_envs; auto using denot_var_inf.
    + destruct es; simpl; congruence.
    + clear; gen_inf_sub_exps.
      induction (length es); constructor; auto; now rewrite 2 Ss_of_nprod_length.
    + revert Infe Hs.
      save_denot_exp se Hse.
      setoid_rewrite denot_exp_eq in Hse; revert Hse; simpl.
      gen_sub_exps.
      unfold eq_rect_r, eq_rect, eq_sym; cases; intros; subst; try congruence.
      eapply Forall2t_lift_nprod; eauto using ok_merge.
  - (* Ecase *)
    eapply safe_exp in Hoc as Hs; eauto using restr_exp.
    apply wt_exp_wl_exp in Hwt as Hwl.
    apply wt_exp_wx_exp in Hwt as Hwx.
    inv Hwt. inv Hwc. inv Hoc. (* inv Hwl. *)
    rewrite <- Forall_map, <- Forall_concat in *.
    inv Hwl. inv Hwx.
    take (restr_exp e) and unshelve eapply IHe in it as He; eauto using infinite_exp; clear IHe.
    apply Forall_impl_inside with (P := wt_exp _ _) in H0; auto.
    apply Forall_impl_inside with (P := wc_exp _ _) in H0; auto.
    take (Forall restr_exp _) and rewrite map_map in it.
    apply Forall_impl_inside with (P := restr_exp) in H0; auto.
    apply Forall_concat in it.
    apply Forall_impl_inside with (P := no_rte_exp _ _ _ _ _) in H0; auto.
    unshelve eapply Forall_concat, sem_sub_expss in H0; eauto using infinite_expss.
    revert Infe (* He *) Hs H0.
    save_denot_exp se Hse.
    revert He; gen_infinite_exp.
    setoid_rewrite denot_exp_eq in Hse; revert Hse; simpl.
    gen_sub_exps.
    unfold eq_rect_r, eq_rect, eq_sym; cases; intros; subst; try congruence.
    eapply ScaseTotal_alt2 with (d:= (Streams.const absent)) in H0;
      eauto using Ss_of_nprod_length.
    + destruct es; simpl; congruence.
    + clear; revert Inf0.
      rewrite Ss_of_nprod_length.
      generalize t0; clear.
      induction (length (map fst es)); constructor; auto using Ss_of_nprod_length.
    + eapply Forall2t_lift_nprod; eauto using ok_case, map_eq_nnil.
  - (* Ecase défaut *)
    eapply safe_exp in Hoc as Hs; eauto using restr_exp.
    apply wt_exp_wl_exp in Hwt as Hwl.
    apply wt_exp_wx_exp in Hwt as Hwx.
    inv Hwt. inv Hwc. inv Hoc.
    inv Hwl. inv Hwx.
    take (wt_exp _ _ e) and eapply safe_exp_ in it as HH; eauto using wf_env_0_ext, wf_env_loc.
    destruct HH as (Tye & _&_). (* on en aura besoin pour prouver wt_streams *)
    take (restr_exp e) and unshelve eapply IHe in it as He; eauto using infinite_exp; clear IHe.
    rewrite <- Forall_map, <- Forall_concat in *.
    rewrite map_id in *.
    apply Forall_impl_inside with (P := wt_exp _ _) in H0, H1; auto.
    apply Forall_impl_inside with (P := wc_exp _ _) in H0, H1; auto.
    apply Forall_impl_inside with (P := restr_exp) in H0, H1; auto.
    apply Forall_impl_inside with (P := no_rte_exp _ _ _ _ _) in H0, H1; auto.
    rewrite Forall_concat, Forall_map in H36, H40. (* pour Forall wl & wx... *)
    apply Forall_concat in H7. (* Forall (Forall restr)) *)
    unshelve eapply Forall_concat, sem_sub_expss in H0; eauto using infinite_expss.
    unshelve eapply sem_sub_exps in H1 as (vd & Eqvd & Semd); eauto using infinite_exps.
    revert Infe Hs Tye H0 Semd Eqvd.
    save_denot_exp se Hse.
    setoid_rewrite denot_exp_eq in Hse; revert Hse; simpl.
    revert He; gen_infinite_exp.
    gen_sub_exps.
    unfold eq_rect_r, eq_rect, eq_sym; cases; try congruence; intros.
    2: now rewrite length_typesof_annots, annots_numstreams in n.
    subst.
    eapply ScaseDefault_alt2 with (d:= (Streams.const absent)) in H0;
      eauto using Ss_of_nprod_length.
    + destruct es; simpl; congruence.
    + (* wt_streams *)
      take (typeof e = _) and rewrite it in *; inv Tye.
      constructor; auto using ty_DS_wt_stream.
    + (* ça va virer un jour *)
      apply Forall2_length in Eqvd.
      rewrite Ss_of_nprod_length in *; auto.
    + clear; revert Inf0.
      rewrite Ss_of_nprod_length.
      generalize t0; clear.
      induction (length (map fst es)); constructor; auto using Ss_of_nprod_length.
    + unfold EqSts in Eqvd. (* pas normal... *)
      rewrite Eqvd.
      (* ici on veut à tout prix utiliser Forall2t_lift_nprod,
         il faut arranger un peu le but pour qu'il ait la bonne forme *)
      apply (Forall2t_more_col _ _ (fun ss ds => case _ (combine _ ss) (Some ds))).
      { now rewrite 2 Ss_of_nprod_length. }
      (* FIXME: c'est horrible de devoir écrire ça *)
      assert (exists Inf,
                 Forall2 EqSts
                   (Ss_of_nprod t0 Inf1 :: Ss_of_nprods t1 Inf0)
                   (Ss_of_nprods (nprod_cons t0 t1) Inf)
             ) as [? ->].
      { clear.
        exists (@forall_nprod_cons _ _ _ _ _ Inf1 Inf0).
        revert_all; intros ??.
        destruct (length (map fst es)).
        - cbn; constructor; auto using _Ss_of_nprod_eq.
        - (* pourquoi deux fois ? j'aimerais savoir *)
          do 2 (constructor; eauto using _Ss_of_nprod_eq, _Ss_of_nprods_eq). }
      eapply (Forall2t_lift_nprod _ (scase_defv (map fst es) t)) in Hs; intros; eauto.
      eapply ok_case_def; eauto using map_eq_nnil.
  - (* Eapp *)
    eapply safe_exp in Hoc as Hs; eauto using restr_exp.
    apply wt_exp_wl_exp in Hwt as Hwl.
    inv Hwt. inv Hwc. inv Hoc. inv Hwl.
    repeat take (find_node _ _ = _) and rewrite it in *.
    repeat take (Some _ = Some _) and inv it.
    apply Forall_impl_inside with (P := wt_exp _ _) in H0,H1; auto.
    apply Forall_impl_inside with (P := wc_exp _ _) in H0,H1; auto.
    apply Forall_impl_inside with (P := restr_exp) in H0,H1; auto.
    apply Forall_impl_inside with (P := no_rte_exp _ _ _ _ _) in H0,H1; auto.
    eapply ok_sem_Eapp; eauto using wc_env_in.
Qed.

Corollary ok_sem_exps :
  forall Γ ins env envI InfΓ bsi,
    let bs := bss ins envI in
    wf_env Γ ins envI bs env ->
    let H := hist_of_envs Γ ins envI env InfΓ in
    forall es,
      Forall restr_exp es ->
      Forall (wt_exp G Γ) es ->
      Forall (wc_exp G Γ) es ->
      Forall (no_rte_exp G ins envG envI env) es ->
      Forall (fun e => forall Infe,
                  sem_exp G H (S_of_DS id bs bsi) e
                    (Ss_of_nprod (denot_exp G ins e envG envI env) Infe)) es.
Proof.
  intros.
  simpl_Forall; eauto using ok_sem_exp.
Qed.


(** Node semantics  *)

Lemma ok_vars_equation :
  forall Γ ins (envI env : DS_prod SI) InfΓ n (np : nprod n) xs tys Inf,
    NoDup (ins ++ xs) ->
    Forall2 (HasType Γ) xs tys -> (* il suffirait de IsVar *)
    Forall2 (fun (x : ident) (s : DS (sampl value)) =>
               s == PROJ (DS_fam SI) x env)
      xs (list_of_nprod np) ->
    Forall2 (sem_var (hist_of_envs Γ ins envI env InfΓ))
      (map Var xs) (Ss_of_nprod np Inf).
Proof.
  clear.
  induction n; intros * Nd Hty Hf;
    inv Hf; inv Hty; constructor; eauto using NoDup_remove_1.
  eapply sem_var_nins; eauto using HasType_IsVar.
  apply NoDup_remove_2 in Nd; contradict Nd.
  now apply in_app_weak.
Qed.

Lemma ok_sem_equation :
  forall Γ xs es ins envI bsi env,
    let bs := bss ins envI in
    Forall restr_exp es ->
    wc_equation G Γ (xs,es) ->
    wt_equation G Γ (xs,es) ->
    NoDup (ins ++ xs) ->
    wf_env Γ ins envI bs env ->
    Forall (no_rte_exp G ins envG envI env) es ->
    (* hypothèse sur [env] qui doit satisfaire les contraintes
       de l'équation; typiquement obtenue avec [denot_blocks_equs] *)
    Forall2 (fun x (s : DS (sampl value)) => s == PROJ _ x env) xs
      (list_of_nprod (denot_exps G ins es envG envI env)) ->
    forall InfΓ,
      sem_equation G (hist_of_envs Γ ins envI env InfΓ) (S_of_DS id bs bsi) (xs,es).
Proof.
  intros * Hr Hwc Hwt Nd Hwf Hop Hxs ?.
  take (wt_equation _ _ _) and inv it.
  take (wc_equation _ _ _) and inv it.
  - (* cas d'un appel dépendant *)
    repeat take (Forall _ [_]) and inv it.
    take (wt_exp _ _ _) and apply wt_exp_wl_exp in it as Hwl.
    inv it. inv Hwl.
    take (no_rte_exp _ _ _ _ _ _) and inv it.
    take (restr_exp _) and inv it.
    take (find_node _ _ = _) and rewrite it in *.
    repeat take (Some _ = Some _) and inv it.
    econstructor.
    repeat constructor.
    eapply ok_sem_Eapp; eauto using wc_env_in, ok_sem_exps, Forall2_length.
    (* maintenant, les variables *)
    apply Forall2_map_1; simpl.
    rewrite denot_exps_eq, denot_exps_nil in Hxs.
    setoid_rewrite list_of_nprod_app in Hxs; simpl in Hxs.
    rewrite app_nil_r in *.
    eapply ok_vars_equation; eauto.
  - (* cas normal *)
    eapply ok_sem_exps, sem_sub_exps in H as (sss & Heqs & Hsem); eauto.
    apply Seq with sss; eauto.
    (* maintenant, les variables *)
    rewrite <- Forall2_map_1, Heqs.
    eapply ok_vars_equation; eauto.
  Unshelve.
  { eapply infinite_exp; eauto.
    constructor; auto.
    eapply wt_exp_wx_exp; econstructor; eauto.
    eapply wt_exp_wl_exp; econstructor; eauto. }
  { eapply infinite_exps; eauto.
    simpl_Forall; eauto using wc_exp_wx_exp.
    simpl_Forall; eauto using wc_exp_wl_exp. }
Qed.

(* on traite tous les blocs d'une liste d'un coup, c'est moins problématique
   dans la gestion des duplications d'identifiants *)
Lemma ok_sem_blocks :
  forall Γ ins (env : DS_prod SI) envI bsi blks,
    let bs := bss ins envI in
    env == denot_blocks G ins blks envG envI env ->
    wf_env Γ ins envI bs env ->
    Forall restr_block blks ->
    NoDup (flat_map get_defined blks ++ ins) ->
    Forall (wt_block G Γ) blks ->
    Forall (wc_block G Γ) blks ->
    Forall (no_rte_block G ins envG envI env) blks ->
    forall InfΓ,
      Forall (sem_block G (hist_of_envs Γ ins envI env InfΓ) (S_of_DS id bs bsi)) blks.
Proof.
  intros Γ ins env envI bsi blks bs Henv Hco Hr Ndi Hwt Hwc Hoc Inf.
  assert (Forall (wl_block G) blks) as Hwl
      by eauto using Forall_impl, wt_block_wl_block.
  assert (NoDup (flat_map get_defined blks)) as Nd
      by eauto using NoDup_app_weaken.
  pose proof (denot_blocks_equs G ins envG envI env blks Hwl Nd) as Hb.
  clear Hwl Nd.
  revert dependent env; intro env; simpl.
  generalize (denot_blocks G ins blks envG envI env).
  intros env' Henv.
  induction blks as [| blk blks]; constructor.
  - inv Hr.
    take (restr_block blk) and inv it.
    simpl_Forall.
    take (wc_block _ _ _) and inv it.
    take (wt_block _ _ _) and inv it.
    constructor.
    eapply ok_sem_equation; eauto.
    + rewrite Permutation_app_comm, app_assoc in Ndi.
      eauto using NoDup_app_weaken.
    + eapply Forall2_impl_In; eauto 1; simpl; intros * ?? ->.
      now rewrite Henv.
  - simpl in Ndi.
    rewrite <- app_assoc in Ndi.
    apply NoDup_app_r in Ndi.
    apply IHblks; auto; now simpl_Forall.
Qed.

(** Pour pouvoir utiliser InfG, Wfg, Hnode, on considère
 * l'ajout d'un nœud en tête de G.(nodes). *)
Lemma ok_sem_node :
  forall (n : node),
    let '(Global tys exts nds) := G in
    Ordered_nodes (Global tys exts (n :: nds)) ->
    restr_node n ->
    wc_node G n ->
    wt_node G n ->
    let f := n_name n in
    let Γ := senv_of_ins (n_in n) ++ senv_of_decls (n_out n) ++ get_locals (n_block n) in
    let ins := map fst (n_in n) in
    forall envI,
    let bs := bss ins envI in
    let envn := FIXP _ (denot_node G n envG envI) in
    let ss := np_of_env ins envI in
    let os := np_of_env (List.map fst (n_out n)) envn in
    wf_env Γ ins envI bs envn ->
    no_rte_node G ins envG envI envn n ->
    inf_dom Γ ins envI envn ->
    forall infI infO,
      sem_node (Global tys exts (n :: nds)) f (Ss_of_nprod ss infI) (Ss_of_nprod os infO).
Proof.
  (* on pose ok_sem_blocks car une fois G détruit, c'est impossible *)
  pose proof ok_sem_blocks as ok_sem_blocks.
  destruct G as [tys exts nds].
  intros n Hord Hr Wc Wt ???????? Hco Hoc InfΓ ??.
  pose (Hn := hist_of_envs Γ ins envI envn InfΓ).
  (* on masque les variables locales pour mieux les exposer dans sem_scope *)
  pose (H := restrict Hn (senv_of_ins (n_in n) ++ senv_of_decls (n_out n))).
  eapply Snode with (H := H); eauto using find_node_now.
  - (* sem_var in *)
    subst H ss.
    apply Forall2_forall2.
    split. { now rewrite Ss_of_nprod_length. }
    intros ?? k ?? Hk **; subst.
    assert (Hk' : k < length (n_in n)) by (rewrite map_length in Hk; auto).
    apply sem_var_restrict.
    { apply IsVar_app; left.
      apply IsVarC, fst_InMembers.
      rewrite map_fst_senv_of_ins; eauto using nth_In. }
    unshelve edestruct Ss_of_nprod_nth as [Inf2 ->]; auto using errTy.
    apply sem_var_ins; auto using nth_In.
    { apply IsVar_app; left.
      apply IsVarC, fst_InMembers.
      rewrite map_fst_senv_of_ins; eauto using nth_In. }
    erewrite nth_np_of_env; eauto.
  - (* sem_var out *)
    subst H os.
    apply Forall2_forall2.
    split. { rewrite Ss_of_nprod_length. now setoid_rewrite map_length. }
    intros ?? k ?? Hk **; subst.
    assert (Hk' : k < length (n_out n)) by (rewrite map_length in Hk; auto).
    apply sem_var_restrict.
    { apply IsVar_app; right.
      apply IsVarC, fst_InMembers.
      rewrite map_fst_senv_of_decls; eauto using nth_In. }
    unshelve edestruct Ss_of_nprod_nth as [Inf2 ->]; auto using errTy.
    apply sem_var_nins.
    { apply IsVar_app; right.
      apply IsVar_app; left.
      apply IsVarC, fst_InMembers.
      rewrite map_fst_senv_of_decls; eauto using nth_In. }
    { intro; eapply (not_in_out n); eauto using nth_In. }
    erewrite nth_np_of_env; auto.
  - (* sem_block *)
    apply sem_block_cons'; eauto using find_node_not_Is_node_in, find_node_now.
    inv Wc. inv Wt.
    inversion_clear Hr as [?? Hrtb (? & Vdc & Perm)].
    inv Hrtb.
    constructor.
    unfold no_rte_node in Hoc.
    pose proof (n_nodup n) as [Nd Ndl].
    take (_ = n_block n) and rewrite <- it in *.
    take (wt_block _ _ _) and inv it.
    take (wt_scope _ _ _ _) and inv it.
    take (wc_block _ _ _) and inv it.
    take (wc_scope _ _ _ _) and inv it.
    inv Vdc.
    take (VarsDefinedCompScope _ _ _) and inversion_clear it as [??? (?& Vd & Perm2)].
    inv Ndl.
    take (NoDupScope _ _ _) and inversion_clear it as [??????].

    assert (Hdom : dom_lb Hn (senv_of_decls locs)). {
      split; intros y Hl.
      - assert (IsVar Γ y)
          by (unfold Γ; rewrite <- it, 2 IsVar_app; simpl; tauto).
        unshelve eapply sem_var_In, sem_hist_of_envs'; try reflexivity; auto.
      - exfalso. inv Hl.
        take (In (_,_) _) and apply in_map_iff in it as (?& Hinv &?).
        simpl_Forall; subst.
        inv Hinv; simpl in *; contradiction.
    }

    (* on extrait les variables locales *)
    apply Sscope with (Hi' := restrict Hn (senv_of_decls locs)).
    { (* dom *) apply dom_restrict, Hdom. }
    unfold H.
    rewrite union_restrict.

    (* on vire péniblement le restrict *)
    eapply Forall_impl_In with (P := sem_block _ Hn _).
    { intros b Hin Hsem.
      eapply Forall2_in_left in Vd as (?& Hin2 &?); eauto.
      simpl_Forall.
      eapply sem_block_restrict; eauto using wt_block_wx_block.
      eapply NoDupLocals_incl; eauto.
      apply incl_concat in Hin2.
      rewrite Perm2, Perm in Hin2.
      solve_incl_app.
    }
    subst ss.
    edestruct clocks_of_bss as [Inf ->]; eauto 2 using NoDup_app_l.
    subst Γ Γ' Γ0 Γ'0.
    (* on simplifie get_locals partout : *)
    revert dependent InfΓ.
    take (_ = n_block n) and rewrite <- it, <- app_assoc in *.
    simpl (get_locals _) in *; intros.
    (* maintenant c'est ok *)
    eapply ok_sem_blocks in Hco; eauto 2 using NoDup_get_defined.
    unfold envn at 1.
    now rewrite FIXP_eq, denot_node_eq, denot_top_block_eq, <- it at 1.
Qed.

Lemma ok_sem_node_test :
  forall (n : node),
    restr_node n ->
    wc_node G n ->
    wt_node G n ->
    let f := n_name n in
    let Γ := senv_of_ins (n_in n) ++ senv_of_decls (n_out n) ++ get_locals (n_block n) in
    let ins := map fst (n_in n) in
    forall envI,
    let bs := bss ins envI in
    let envn := FIXP _ (denot_node G n envG envI) in
    let ss := np_of_env ins envI in
    let os := np_of_env (List.map fst (n_out n)) envn in
    wf_env Γ ins envI bs envn ->
    no_rte_node G ins envG envI envn n ->
    inf_dom Γ ins envI envn ->
    forall infI infO,
      sem_node G f (Ss_of_nprod ss infI) (Ss_of_nprod os infO).
Proof.
Admitted.

End Ok_node.

Section TESTMAIN.

Definition no_rte_global_main {PSyn Prefs} (G : @global PSyn Prefs) main envI :=
  let envG := denot_global G in
  Forall (fun n =>
            let ins := List.map fst n.(n_in) in
            if ident_eqb (n_name n) main
            then no_rte_node G ins envG envI (envG (n_name n) envI) n
            else forall envI, no_rte_node G ins envG envI (envG (n_name n) envI) n)
    (nodes G).

(* commenter : nécessite malheureusement ordered_nodes *)
Theorem noerrors_prog :
  forall {PSyn Prefs} (G : @global PSyn Prefs),
    wt_global G ->
    wc_global G ->
    forall f n envI,
      no_rte_global_main G f envI ->
      find_node f G = Some n ->
      let ins := List.map fst n.(n_in) in
      let Γ := senv_of_ins (n_in n) ++ senv_of_decls (n_out n) ++ get_locals (n_block n) in
      forall bs, bss ins envI <= bs ->
      wf_env Γ ins envI bs 0 ->
      wf_env Γ ins envI bs (denot_global G f envI).
Proof.
  intros * Wtg Wcg * Norte Hfind ??? Hle Hins.
  unfold no_rte_global_main in Norte.
  assert (Ordered_nodes G) as Hord.
  now apply wl_global_Ordered_nodes, wt_global_wl_global.
  remember (denot_global G) as envG eqn:HG.
  assert (forall f nd envI,
             find_node f G = Some nd ->
             envG f envI == FIXP _ (denot_node G nd envG envI)) as HenvG.
  { intros * Hf; subst.
    unfold denot_global.
    now rewrite <- PROJ_simpl, FIXP_eq, PROJ_simpl, denot_global_eq, Hf at 1. }
  clear HG. (* maintenant HenvG contient tout ce qu'on doit savoir sur envG *)
  revert Norte.
  revert dependent n. revert f envI. revert bs.
  destruct G as [tys exts nds].
  induction nds as [|a nds]; intros. inv Hfind.
  destruct (ident_eq_dec (n_name a) f); subst.
  - (* cas qui nous intéresse *)
    rewrite find_node_now in Hfind; inv Hfind; auto.
    inversion_clear Norte as [|?? Hoc Hocs].
    rewrite ident_eqb_refl in Hoc.
    (* specialize (Hoc envI bs (wf_env_loc _ _ _ _ Hins)). *)
    revert Hoc. fold ins.
    rewrite HenvG; auto using find_node_now.
    rewrite <- denot_node_cons;
      eauto using find_node_not_Is_node_in, find_node_now.
    rewrite FIXP_fixp.
    intro Hoc.
    apply no_rte_node_cons in Hoc; eauto using find_node_not_Is_node_in, find_node_now.
    apply fixp_inv2_le with
      (Q := fun env =>
              no_rte_node {| types := tys; externs := exts; nodes := nds |} ins envG envI env n
      ); eauto using wf_env_admissible, oc_node_admissible_rev, wf_env_0_ext.
    intros env Hsafe Hl Hoc2.
    apply Ordered_nodes_cons in Hord as Hord'.
    apply wt_global_cons in Wtg as Wtg'.
    destruct Wtg as [? Wtp] eqn:HH; clear HH. (* trouver un autre moyen de garder Wtg *)
    inv Wcg. inv Wtp. (* inv Rg. *)
    apply safe_node; auto; try tauto.
    (* reste l'hypothèse de récurrence sur les nœuds *)
    intros f2 n2 Hfind ?? bs2 envI2 Hbs2 Hins2.
    apply wf_env_loc.
    apply IHnds; auto using wf_env_0_ext.
    + (* montrons que HenvG tient toujours *)
      intros f' ndf' envI' Hfind'.
      eapply find_node_uncons with (nd := n) in Hfind' as ?; auto.
      rewrite HenvG, <- denot_node_cons; eauto using find_node_later_not_Is_node_in.
    + (* montrons que no_rte tient toujours *)
      simpl (nodes _).
      take (wc_node _ _ /\ _) and destruct it as [? Hnn].
      clear - Hocs Hnn Hord.
      simpl_Forall.
      rewrite <- ident_eqb_neq, ident_eqb_sym in Hnn.
      rewrite Hnn in Hocs.
      cases_eqn HH; intros; eapply no_rte_node_cons; eauto using Ordered_nodes_nin.
  - rewrite find_node_other in Hfind; auto.
    apply IHnds; auto.
    + eauto using wt_global_cons.
    + eauto using wc_global_cons.
    + eauto using Ordered_nodes_cons.
    + intros f' ndf' envI' Hfind'.
      eapply find_node_uncons with (nd := a) in Hfind' as ?; auto.
      rewrite HenvG, <- denot_node_cons; eauto using find_node_later_not_Is_node_in.
    + clear - Norte Hord. inv Norte.
      eapply Forall_impl_In; eauto.
      simpl; intros * Hin HH *.
      cases_eqn HH; intros; eapply no_rte_node_cons; eauto using Ordered_nodes_nin.
Qed.


Theorem _ok_global :
  forall (HasCausInj : forall (Γ : static_env) (x cx : ident), HasCaus Γ x cx -> cx = x),
  forall {PSyn Prefs} (G : @global PSyn Prefs),
    restr_global G ->
    wt_global G ->
    wc_global G ->
    Forall node_causal (nodes G) ->
    forall f n envI,
      no_rte_global_main G f envI ->
      find_node f G = Some n ->
      let ins := map fst (n_in n) in
      let outs := map fst (n_out n) in
      let xs := np_of_env ins envI in
      let os := np_of_env outs (denot_global G f envI) in
      wf_ins n envI (bss ins envI) ->
      infinite_dom envI ins ->
      exists InfI InfO,
        sem_node G f (Ss_of_nprod xs InfI) (Ss_of_nprod os InfO).
Proof.
  intros ???? Rg Wtg Wcg Causg ??? Norte Hfind ???? Hins InfI.
  assert (Ordered_nodes G) as Hord.
  { now apply wl_global_Ordered_nodes, wt_global_wl_global. }
  pose proof (SafeG := noerrors_prog G Wtg Wcg (* f n envI Norte Hfind *)).
  unfold no_rte_global_main in Norte, SafeG.
  pose proof (Halign := wf_alignLE G Rg).
  remember (denot_global G) as envG eqn:HG.
  assert (InfG : forall f nd envI,
       find_node f G = Some nd ->
       infinite_dom envI (map fst (n_in nd)) ->
       infinite_dom (envG f envI) (map fst (n_out nd) ++ map fst (get_locals (n_block nd)))).
  { subst envG. eauto using denot_inf. }
  assert (AbsG : forall f envI,
             envG f (APP_env abs_env envI) <= APP_env abs_env (envG f envI)).
  { intros; subst;  auto using abs_indep_global. }
  assert (Hlp : forall f X n, envG f (take_env n X) == take_env n (envG f X)).
  { intros; subst; auto using lp_global. }
  assert (HenvG : forall f nd envI,
             find_node f G = Some nd ->
             envG f envI == FIXP _ (denot_node G nd envG envI)).
  { intros * Hf; subst.
    unfold denot_global.
    now rewrite <- PROJ_simpl, FIXP_eq, PROJ_simpl, denot_global_eq, Hf at 1. }
  (* HenvG est tout ce qu'il faut savoir sur la définition de envG *)
  clear HG.
  pose proof (InfG _ _ _ Hfind InfI) as Infol.
  apply infinite_dom_app_l in Infol.
  exists (inf_dom_np_of_env _ _ InfI), (inf_dom_np_of_env _ _ Infol).
  remember (inf_dom_np_of_env _ _ _) as Infi eqn:HH; clear HH.
  remember (inf_dom_np_of_env _ _ _) as Info eqn:HH; clear HH.
  fold xs os in Info, Infi.

  eapply ok_sem_node_test.
  revert dependent n.
  revert dependent envI.
  revert f.
  destruct G as [tys exts nds].
  induction nds as [|a nds]; intros. { inv Hfind. }
  destruct (ident_eq_dec (n_name a) f); subst.
  - (* cas du nœud courant *)
    rewrite find_node_now in Hfind; auto; inv Hfind.
    subst os outs.
    edestruct (Ss_of_nprod_eq _ Info) as [Inf3 ->].
    { rewrite HenvG, <- denot_node_cons;
        eauto using find_node_not_Is_node_in, find_node_now.
    }
    apply wt_global_uncons in Wtg as Wtn.
    apply wt_global_cons in Wtg as Wtg'.
    apply wc_global_uncons in Wcg as Wcn.
    inversion Rg; subst.
    inversion Wcg; subst.
    inversion Wtg; subst.
    eapply ok_sem_node_test in Wtg' as Hsem;
      eauto using wf_env_loc, wf_env_0_ext, infinite_dom_app_l, find_node_uncons.
    { eapply Hsem; eauto.
      all: rewrite (denot_node_cons _ n);
        eauto using find_node_not_Is_node_in, find_node_now.
      all: rewrite <- HenvG; auto using find_node_now.
      - (* wf_env *)
        eapply SafeG; auto using find_node_now, wf_env_loc, wf_env_0_ext.
      - (* no_rte *)
        inversion_clear Norte as [|?? Nort].
        rewrite ident_eqb_refl in Nort.
        apply (no_rte_node_cons n); eauto using find_node_not_Is_node_in, find_node_now.
      - (* inf_dom *)
        eapply inf_dom_decomp in InfG; eauto using find_node_now.
        now rewrite 2 map_app, map_fst_senv_of_ins, map_fst_senv_of_decls.
    }{(* wf_env *)
      clear IHnds. clear AbsG . clear dependent xs.  simpl (nodes _ ) in *.
      intros f' n' envI' Hfind' ins' Γ' bs' Hbs' Hins'.
      eapply SafeG; eauto using find_node_uncons.
    }
    (* plus qu'à utiliser IHnds *)
    inv Causg. inversion Hord; subst.
    intros; apply IHnds; auto.
    + admit.
    + eauto using find_node_uncons.
    + eauto using find_node_uncons.
    + intros f' ndf' envI' Hfind'.
      eapply find_node_uncons with (nd := n) in Hfind' as ?; auto.
      rewrite HenvG, <- denot_node_cons; eauto using find_node_later_not_Is_node_in.
    + admit.
    + eauto using infinite_dom_np.
    + eauto using infinite_dom_np.
  - (* cas de récurrence *)
    rewrite find_node_other in Hfind; auto.
    apply sem_node_cons'; auto.
    apply IHnds; auto.
    + now inv Rg.
    + eauto using wt_global_cons.
    + eauto using wc_global_cons.
    + now inv Causg.
    + eauto using Ordered_nodes_cons.
    + clear IHnds.
      intros.
      eapply SafeG; auto.
      eapply Forall_impl_In, H; simpl; intros.
      cases_eqn HH; intros; eapply no_rte_node_cons; eauto using Ordered_nodes_nin.



      (*   clear - Norte Hord. inv Norte. *)
    (*   eapply Forall_impl_In; eauto. *)
    (*   intros * Hin HH ?. *)
    (*   eapply no_rte_node_cons in HH; eauto using Ordered_nodes_nin. *)
      admit.
    + admit.
    + intros f' ndf' envI' Hfind'.
      eapply find_node_uncons with (nd := a) in Hfind' as ?; eauto.
    + intros f' ndf' envI' Hfind'.
      eapply find_node_uncons with (nd := a) in Hfind' as ?; auto.
      rewrite HenvG, <- denot_node_cons; eauto using find_node_later_not_Is_node_in.
    + inversion_clear Norte as [|??? Nort].
      eapply Forall_impl_In, Nort; simpl; intros.
      cases_eqn HH; intros; eapply no_rte_node_cons; eauto using Ordered_nodes_nin.
Qed.


End TESTMAIN.




Theorem _ok_global :
  forall (HasCausInj : forall (Γ : static_env) (x cx : ident), HasCaus Γ x cx -> cx = x),
  forall {PSyn Prefs} (G : @global PSyn Prefs),
    restr_global G ->
    wt_global G ->
    wc_global G ->
    no_rte_global G ->
    Forall node_causal (nodes G) ->
    forall f n envI,
      find_node f G = Some n ->
      let ins := map fst (n_in n) in
      let outs := map fst (n_out n) in
      let xs := np_of_env ins envI in
      let os := np_of_env outs (denot_global G f envI) in
      wf_ins n envI (bss ins envI) ->
      infinite_dom envI ins ->
      exists InfI InfO,
        sem_node G f (Ss_of_nprod xs InfI) (Ss_of_nprod os InfO).
Proof.
  intros ???? Rg Wtg Wcg Ocg Causg ??? Hfind ???? Hins InfI.
  unfold no_rte_global in Ocg.
  assert (Ordered_nodes G) as Hord.
  { now apply wl_global_Ordered_nodes, wt_global_wl_global. }
  pose proof (SafeG := noerrors_prog G Wtg Wcg Ocg).
  pose proof (Halign := wf_alignLE G Rg).
  remember (denot_global G) as envG eqn:HG.
  assert (InfG : forall f nd envI,
       find_node f G = Some nd ->
       infinite_dom envI (map fst (n_in nd)) ->
       infinite_dom (envG f envI) (map fst (n_out nd) ++ map fst (get_locals (n_block nd)))).
  { subst envG. eauto using denot_inf. }
  assert (AbsG : forall f envI,
             envG f (APP_env abs_env envI) <= APP_env abs_env (envG f envI)).
  { intros; subst;  auto using abs_indep_global. }
  assert (Hlp : forall f X n, envG f (take_env n X) == take_env n (envG f X)).
  { intros; subst; auto using lp_global. }
  assert (HenvG : forall f nd envI,
             find_node f G = Some nd ->
             envG f envI == FIXP _ (denot_node G nd envG envI)).
  { intros * Hf; subst.
    unfold denot_global.
    now rewrite <- PROJ_simpl, FIXP_eq, PROJ_simpl, denot_global_eq, Hf at 1. }
  (* HenvG est tout ce qu'il faut savoir sur la définition de envG *)
  clear HG.
  pose proof (InfG _ _ _ Hfind InfI) as Infol.
  apply infinite_dom_app_l in Infol.
  exists (inf_dom_np_of_env _ _ InfI), (inf_dom_np_of_env _ _ Infol).
  remember (inf_dom_np_of_env _ _ _) as Infi eqn:HH; clear HH.
  remember (inf_dom_np_of_env _ _ _) as Info eqn:HH; clear HH.
  fold xs os in Info, Infi.
  revert dependent n.
  revert dependent envI.
  revert f.
  destruct G as [tys exts nds].
  induction nds as [|a nds]; intros. { inv Hfind. }
  destruct (ident_eq_dec (n_name a) f); subst.
  - (* cas du nœud courant *)
    rewrite find_node_now in Hfind; auto; inv Hfind.
    subst os outs.
    edestruct (Ss_of_nprod_eq _ Info) as [Inf3 ->].
    { rewrite HenvG, <- denot_node_cons;
        eauto using find_node_not_Is_node_in, find_node_now.
    }
    apply wt_global_uncons in Wtg as Wtn.
    apply wt_global_cons in Wtg as Wtg'.
    apply wc_global_uncons in Wcg as Wcn.
    inversion Rg; subst.
    inversion Wcg; subst.
    inversion Wtg; subst.
    eapply ok_sem_node in Wtg' as Hsem;
      eauto using wf_env_loc, wf_env_0_ext, infinite_dom_app_l, find_node_uncons.
    { eapply Hsem; eauto.
      all: rewrite (denot_node_cons _ n);
        eauto using find_node_not_Is_node_in, find_node_now.
      all: rewrite <- HenvG; auto using find_node_now,
        wf_env_loc, wf_env_0_ext.
      - (* no_rte *)
        inv Ocg. apply (no_rte_node_cons n);
          eauto using find_node_not_Is_node_in, find_node_now.
      - (* inf_dom *)
        eapply inf_dom_decomp in InfG; eauto using find_node_now.
        now rewrite 2 map_app, map_fst_senv_of_ins, map_fst_senv_of_decls.
    }
    (* plus qu'à utiliser IHnds *)
    inv Causg. inversion Hord; subst.
    intros; apply IHnds; auto.
    + clear - Ocg Hord. inv Ocg.
      eapply Forall_impl_In; eauto.
      intros * Hin HH ?.
      eapply no_rte_node_cons in HH; eauto using Ordered_nodes_nin.
    + eauto using find_node_uncons.
    + eauto using find_node_uncons.
    + eauto using find_node_uncons.
    + intros f' ndf' envI' Hfind'.
      eapply find_node_uncons with (nd := n) in Hfind' as ?; auto.
      rewrite HenvG, <- denot_node_cons; eauto using find_node_later_not_Is_node_in.
    + eauto using infinite_dom_np.
    + eauto using infinite_dom_np.
  - (* cas de récurrence *)
    rewrite find_node_other in Hfind; auto.
    apply sem_node_cons'; auto.
    apply IHnds; auto.
    + now inv Rg.
    + eauto using wt_global_cons.
    + eauto using wc_global_cons.
    + clear - Ocg Hord. inv Ocg.
      eapply Forall_impl_In; eauto.
      intros * Hin HH ?.
      eapply no_rte_node_cons in HH; eauto using Ordered_nodes_nin.
    + now inv Causg.
    + eauto using Ordered_nodes_cons.
    + intros f' ndf' envI' Hfind'.
      eapply find_node_uncons with (nd := a) in Hfind' as ?; eauto.
    + intros f' ndf' Hfind'.
      eapply find_node_uncons with (nd := a) in Hfind' as ?; eauto.
    + intros f' ndf' envI' Hfind'.
      eapply find_node_uncons with (nd := a) in Hfind' as ?; auto.
    + intros f' ndf' envI' Hfind'.
      eapply find_node_uncons with (nd := a) in Hfind' as ?; auto.
      rewrite HenvG, <- denot_node_cons; eauto using find_node_later_not_Is_node_in.
Qed.

(** Autre formulation, en fournissant un nprod plutôt qu'un environnement en entrée *)
Corollary _ok_global2 :
  forall (HasCausInj : forall (Γ : static_env) (x cx : ident), HasCaus Γ x cx -> cx = x),
  forall {PSyn Prefs} (G : @global PSyn Prefs),
    restr_global G ->
    wt_global G ->
    wc_global G ->
    no_rte_global G ->
    Forall node_causal (nodes G) ->
    forall f n (ss : nprod (length (n_in n))),
      find_node f G = Some n ->
      let ins := idents (n_in n) in
      let envI := env_of_np ins ss in
      let os := np_of_env (List.map fst (n_out n)) (denot_global G f envI) in
      let bs := bss ins envI in
      wf_ins n envI bs ->
      forall InfSs InfO,
        sem_node G f (Ss_of_nprod ss InfSs) (Ss_of_nprod os InfO).
Proof.
  intros ???? Rg Wtg Wcg Ocg Causg ??? Hfind ???? Hins ??.
  edestruct _ok_global as (?&?& Hsem); eauto using inf_dom_env_of_np.
  eapply sem_node_morph in Hsem; eauto using _Ss_of_nprod_eq.
  subst envI os ins; clear.
  revert dependent ss.
  rewrite <- (map_length fst).
  intros; apply _Ss_of_nprod_eq, np_of_env_of_np.
  rewrite map_length; apply n_ingt0.
  destruct (n_nodup n); eauto using NoDup_app_weaken.
Qed.

Definition wf_inputs {PSyn Prefs} (n : @node PSyn Prefs) (ss : nprod (length (n_in n))) :=
  let ins := idents (n_in n) in
  let envI := env_of_np ins ss in
  let bs := bss ins envI in
  let Γ := senv_of_ins (n_in n) ++ senv_of_decls (n_out n) in
  wf_env Γ ins envI bs 0.

(** Witness of the relational semantics *)
Theorem ok_global :
  forall (HasCausInj : forall (Γ : static_env) (x cx : ident), HasCaus Γ x cx -> cx = x),
  forall {PSyn Prefs} (G : @global PSyn Prefs),
    restr_global G ->
    wt_global G ->
    wc_global G ->
    (* no_rte_global G -> *)
    check_global G = true ->
    Forall node_causal (nodes G) ->
    forall f n, find_node f G = Some n ->
    forall (xs : nprod (length (n_in n))) InfXs,
      wf_inputs n xs ->
      exists (os : nprod ((length (n_out n)))) InfO,
        sem_node G f (Ss_of_nprod xs InfXs) (Ss_of_nprod os InfO).
Proof.
  intros ???? Hr Hwt Hwc Hoc Hcaus Hfind ???? Hins.
  apply check_global_ok in Hoc; auto.
  unshelve eapply _ok_global2 with (InfSs := InfXs) in Hins; eauto.
  { eapply inf_dom_np_of_env, infinite_dom_app_l, denot_inf;
      eauto using inf_dom_env_of_np. }
  unfold decl.
  rewrite <- (map_length fst (n_out n)); eauto.
Qed.

End SDTOREL.

Module SdtorelFun
       (Ids   : IDS)
       (Op    : OPERATORS)
       (OpAux : OPERATORS_AUX Ids Op)
       (Cks   : CLOCKS        Ids Op OpAux)
       (Senv  : STATICENV     Ids Op OpAux Cks)
       (Syn   : LSYNTAX       Ids Op OpAux Cks Senv)
       (Typ   : LTYPING       Ids Op OpAux Cks Senv Syn)
       (Cl    : LCLOCKING     Ids Op OpAux Cks Senv Syn)
       (Caus  : LCAUSALITY    Ids Op OpAux Cks Senv Syn)
       (Lord  : LORDERED      Ids Op OpAux Cks Senv Syn)
       (Str   : COINDSTREAMS  Ids Op OpAux Cks)
       (Sem   : LSEMANTICS Ids Op OpAux Cks Senv Syn Lord Str)
       (Den   : SD         Ids Op OpAux Cks Senv Syn Lord)
       (Restr : LRESTR     Ids Op OpAux Cks Senv Syn)
       (Inf   : LDENOTINF  Ids Op OpAux Cks Senv Syn Typ Caus Lord Restr Den)
       (Ckop  : CHECKOP       Ids Op OpAux Cks Senv Syn)
       (OpErr : OP_ERR        Ids Op OpAux Cks Senv Syn Typ Restr Lord Den Ckop)
       (Safe  : LDENOTSAFE Ids Op OpAux Cks Senv Syn Typ Restr Cl Lord Den Ckop OpErr)
       (Abs   : ABS_INDEP  Ids Op OpAux Cks Senv Syn Typ Lord Den)
       (Lp    : LP         Ids Op OpAux Cks Senv Syn Typ Lord Den)
<: SDTOREL Ids Op OpAux Cks Senv Syn Typ Cl Caus Lord Str Sem Den Restr Inf Ckop OpErr Safe Abs Lp.
  Include SDTOREL Ids Op OpAux Cks Senv Syn Typ Cl Caus Lord Str Sem Den Restr Inf Ckop OpErr Safe Abs Lp.
End SdtorelFun.
