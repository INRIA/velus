From Coq Require Import Streams.
From Coq Require Import List.
Import List.ListNotations.
Open Scope list_scope.
From Coq Require Import Omega.

From Coq Require Import Sorting.Permutation.
From Coq Require Import Setoid.
From Coq Require Import Morphisms.

From Coq Require Import FSets.FMapPositive.
From Velus Require Import Common.
From Velus Require Import CommonList.
From Velus Require Import Environment.
From Velus Require Import Operators.
From Velus Require Import CoindStreams IndexedStreams.
From Velus Require Import CoindIndexed.
From Velus Require Import Clocks.
From Velus Require Import Lustre.LSyntax Lustre.LTyping Lustre.LClocking Lustre.LCausality Lustre.LOrdered.
From Velus Require Import Lustre.LSemantics.
From Velus Require Import Lustre.LSemDeterminism.

Module Type LCLOCKSEMANTICS
       (Import Ids   : IDS)
       (Import Op    : OPERATORS)
       (Import OpAux : OPERATORS_AUX Ids Op)
       (Import Cks   : CLOCKS        Ids Op OpAux)
       (Import Syn   : LSYNTAX Ids Op OpAux Cks)
       (Import Clo   : LCLOCKING Ids Op OpAux Cks Syn)
       (LCA          : LCAUSALITY Ids Op OpAux Cks Syn)
       (Import Lord  : LORDERED Ids Op OpAux Cks Syn)
       (Import CStr  : COINDSTREAMS Ids Op OpAux Cks)
       (Import Sem   : LSEMANTICS Ids Op OpAux Cks Syn Lord CStr).

  Import CStr.
  Module IStr := IndexedStreamsFun Ids Op OpAux Cks.
  Module Import CIStr := CoindIndexedFun Ids Op OpAux Cks CStr IStr.

  Module Import Det := LSemDeterminismFun Ids Op OpAux Cks Syn Clo LCA Lord CStr Sem.

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

  Lemma sem_clock_refines : forall H H' ck bs bs',
      Env.refines (@EqSt _) H H' ->
      sem_clock H bs ck bs' ->
      sem_clock H' bs ck bs'.
  Proof.
    cofix CoFix; destruct ck; intros * Href Hsem.
    - inv Hsem; constructor; auto.
    - inv Hsem.
      + econstructor; eauto.
        * eapply sem_var_refines; eauto.
        * eapply CoFix; [|eauto]. eapply history_tl_refines; eauto.
      + econstructor; eauto.
        * eapply sem_var_refines; eauto.
        * eapply CoFix; [|eauto]. eapply history_tl_refines; eauto.
      + eapply Son_abs2; eauto.
        * eapply sem_var_refines; eauto.
        * eapply CoFix; [|eauto]. eapply history_tl_refines; eauto.
  Qed.

  Lemma history_tl_same_find : forall H H' vars,
      Forall (fun x => orel (EqSt (A:=svalue)) (Env.find x H) (Env.find x H')) vars ->
      Forall (fun x => orel (EqSt (A:=svalue)) (Env.find x (history_tl H)) (Env.find x (history_tl H'))) vars.
  Proof.
    intros * Hsem.
    eapply Forall_impl; [|eauto]. intros; simpl in *.
    destruct (Env.find a H) eqn:Hfind; inv H0.
    - symmetry in H2.
      apply history_tl_find_Some in Hfind. apply history_tl_find_Some in H2.
      rewrite Hfind, H2. constructor. rewrite H3; reflexivity.
    - symmetry in H1.
      apply history_tl_find_None in Hfind. apply history_tl_find_None in H1.
      rewrite Hfind, H1. constructor.
  Qed.

  Lemma sem_var_same_find : forall H H' vars id vs,
      Forall (fun x => orel (EqSt (A:=svalue)) (Env.find x H') (Env.find x H)) vars ->
      In id vars ->
      sem_var H id vs ->
      sem_var H' id vs.
  Proof.
    intros * Hf Hin Hsem.
    eapply Forall_forall in Hf; eauto.
    inv Hsem.
    apply Env.find_1 in H1. rewrite H1 in Hf. inv Hf.
    econstructor. eapply Env.find_2; eauto.
    rewrite H2, H4; reflexivity.
  Qed.

  Lemma sem_clock_same_find : forall H H' vars ck bs bs',
      wc_clock vars ck ->
      Forall (fun x => orel (EqSt (A:=svalue)) (Env.find x H') (Env.find x H)) (map fst vars) ->
      sem_clock H bs ck bs' ->
      sem_clock H' bs ck bs'.
  Proof.
    cofix CoFix; destruct ck; intros * Hwc Hf Hsem.
    - inv Hsem; constructor; auto.
    - inv Hwc; inv Hsem.
      + econstructor; eauto.
        * eapply sem_var_same_find; eauto.
          apply in_map_iff. exists (i, ck); auto.
        * eapply CoFix; [| |eauto]. 1:constructor; eauto.
          apply history_tl_same_find; auto.
      + econstructor; eauto.
        * eapply sem_var_same_find; eauto.
          apply in_map_iff. exists (i, ck); auto.
        * eapply CoFix; [| |eauto]. 1:constructor; eauto.
          apply history_tl_same_find; auto.
      + eapply Son_abs2; eauto.
        * eapply sem_var_same_find; eauto.
          apply in_map_iff. exists (i, ck); auto.
        * eapply CoFix; [| |eauto]. 1:constructor; eauto.
          eapply history_tl_same_find; auto.
  Qed.

  Fact sem_var_restrict {B} : forall (vars : list (ident * B)) H id ty v,
      In (id, ty) vars ->
      sem_var H id v ->
      sem_var (Env.restrict H (List.map fst vars)) id v.
  Proof.
    intros vars H id ty v HIn Hsem.
    inv Hsem.
    econstructor; eauto.
    apply Env.find_1 in H1. apply Env.find_2.
    apply Env.restrict_find; auto.
    apply in_map_iff. exists (id, ty); auto.
  Qed.

  Fact sem_exp_restrict {prefs} : forall (G : @global prefs) vars H b e vs,
      wc_exp G vars e ->
      sem_exp G H b e vs ->
      sem_exp G (Env.restrict H (List.map fst vars)) b e vs.
  Proof with eauto.
    induction e using exp_ind2; intros vs Hwt Hsem; inv Hwt; inv Hsem.
    - (* const *) constructor...
    - (* enum *) constructor...
    - (* var *) constructor. eapply sem_var_restrict...
    - (* var (anon) *) constructor. eapply sem_var_restrict...
    - (* unop *)
      econstructor...
    - (* binop *)
      econstructor...
    - (* fby *)
      econstructor...
      + repeat rewrite_Forall_forall. eapply H0...
      + repeat rewrite_Forall_forall. eapply H1...
    - (* arrow *)
      econstructor...
      + repeat rewrite_Forall_forall. eapply H0...
      + repeat rewrite_Forall_forall. eapply H1...
    - (* when *)
      econstructor...
      + repeat rewrite_Forall_forall. eapply H0...
      + eapply sem_var_restrict...
    - (* merge *)
      econstructor...
      + eapply sem_var_restrict...
      + do 2 (eapply Forall2_impl_In; [|eauto]; intros).
        do 2 (eapply Forall_forall in H6; eauto).
        do 2 (eapply Forall_forall in H0; eauto).
    - (* case *)
      econstructor...
      + clear H21. do 2 (eapply Forall2_impl_In; [|eauto]; intros; subst).
        do 2 (eapply Forall_forall in H0; eauto; simpl in * ).
        eapply Forall_forall in H9; eauto.
      + eapply Forall2_impl_In; [|eauto]; intros; subst.
        eapply Forall_forall in H1; eauto.
        eapply Forall_forall in H12; eauto.
    - (* app *)
      econstructor...
      1,2:repeat rewrite_Forall_forall.
      eapply H0... eapply H1...
  Qed.

  Lemma sem_equation_restrict {prefs} : forall (G : @global prefs) vars H b eq,
      wc_equation G vars eq ->
      sem_equation G H b eq ->
      sem_equation G (Env.restrict H (List.map fst vars)) b eq.
  Proof with eauto.
    intros G vars H b [xs es] Hwc Hsem.
    destruct Hwc as (?&?&?). inv Hsem.
    econstructor.
    + repeat rewrite_Forall_forall; eauto.
      eapply sem_exp_restrict...
    + repeat rewrite_Forall_forall.
      eapply sem_var_restrict...
      Unshelve. eapply Cbase.
  Qed.

  Lemma sem_block_restrict {prefs} : forall (G: @global prefs) vars d H b,
      wc_block G vars d ->
      sem_block G H b d ->
      sem_block G (Env.restrict H (List.map fst vars)) b d.
  Proof.
    induction d using block_ind2; intros * Hwc Hsem; inv Hwc; inv Hsem.
    - econstructor.
      eapply sem_equation_restrict; eauto.
    - econstructor; eauto.
      + eapply sem_exp_restrict; eauto.
      + intros k; specialize (H11 k).
        rewrite Forall_forall in *. intros ? Hin.
        eapply sem_block_refines; [|eapply H]; eauto.
        now setoid_rewrite <-Env.restrict_map.
  Qed.

  Corollary sem_blocks_restrict {prefs} : forall (G: @global prefs) vars H b blocks,
      Forall (wc_block G vars) blocks ->
      Forall (sem_block G H b) blocks ->
      Forall (sem_block G (Env.restrict H (List.map fst vars)) b) blocks.
  Proof.
    intros.
    rewrite Forall_forall in *. intros ? Hin.
    eapply sem_block_restrict; eauto.
  Qed.

  (** * Alignment proof *)

  Local Ltac simpl_ndup Hnd :=
    simpl in *;
    try rewrite app_nil_r in Hnd; repeat rewrite map_app.
  Local Ltac ndup_l H := rewrite app_assoc in H; apply NoDupMembers_app_l in H; auto.
  Local Ltac ndup_r H := rewrite Permutation_swap in H; apply NoDupMembers_app_r in H; auto.

  (** ** Semantics with anonymous streams *)
  (** In this intermediate semantics, we force streams produced by functions
      to appear in the environnement.
   *)
  Section AnonSemantics.
    Definition anon_app H (lann : list (type * nclock)) vss :=
      Forall2 (fun '(_, (_, o)) vs => LiftO True (fun x => sem_var H x vs) o) lann vss.

    Lemma anon_app_refines :
      Proper (Env.refines (EqSt (A:=svalue)) ==> eq ==> eq ==> Basics.impl) anon_app.
    Proof.
      unfold anon_app.
      intros ??????????; subst.
      eapply Forall2_impl_In; [|eauto]. intros (?&?&[|]) ? _ _ ?; simpl in *; auto.
      eapply sem_var_refines; eauto.
    Qed.
    Hint Resolve anon_app_refines.

    Context {prefs : PS.t}.
    Variable (G: @global prefs).

    Inductive anon_sem_exp (H : history) (bs : Stream bool) : exp -> Prop :=
    | Aconst : forall c,
        anon_sem_exp H bs (Econst c)
    | Aenum : forall k ty,
        anon_sem_exp H bs (Eenum k ty)
    | Avar : forall x ann,
        anon_sem_exp H bs (Evar x ann)
    | Aunop : forall op e1 ann,
        anon_sem_exp H bs e1 ->
        anon_sem_exp H bs (Eunop op e1 ann)
    | Abinop : forall op e1 e2 ann,
        anon_sem_exp H bs e1 ->
        anon_sem_exp H bs e2 ->
        anon_sem_exp H bs (Ebinop op e1 e2 ann)
    | Afby : forall e0s e1s anns,
        Forall (anon_sem_exp H bs) e0s ->
        Forall (anon_sem_exp H bs) e1s ->
        anon_sem_exp H bs (Efby e0s e1s anns)
    | Aarrow : forall e0s e1s anns,
        Forall (anon_sem_exp H bs) e0s ->
        Forall (anon_sem_exp H bs) e1s ->
        anon_sem_exp H bs (Earrow e0s e1s anns)
    | Awhen : forall es x kty anns,
        Forall (anon_sem_exp H bs) es ->
        anon_sem_exp H bs (Ewhen es x kty anns)
    | Amerge : forall xty es anns,
        Forall (Forall (anon_sem_exp H bs)) es ->
        anon_sem_exp H bs (Emerge xty es anns)
    | Acase : forall e es d anns,
        anon_sem_exp H bs e ->
        Forall (fun oes => forall es, oes = Some es -> Forall (anon_sem_exp H bs) es) es ->
        Forall (anon_sem_exp H bs) d ->
        anon_sem_exp H bs (Ecase e es d anns)
    | Aapp : forall f es er anns,
        Forall (anon_sem_exp H bs) es ->
        Forall (anon_sem_exp H bs) er ->
        (exists xs rs r ys,
            Forall2 (sem_exp G H bs) es xs /\
            Forall2 (fun e r => sem_exp G H bs e [r]) er rs /\
            bools_ofs rs r /\
            (forall k, sem_node G f (map (maskv k r) (concat xs)) (map (maskv k r) ys)) /\
            anon_app H anns ys) ->
        anon_sem_exp H bs (Eapp f es er anns).

    Definition anon_sem_equation H bs (equ : equation) :=
      Forall (anon_sem_exp H bs) (snd equ).

    Hint Constructors anon_sem_exp.

    Lemma anon_sem_exp_refines : forall H1 H2 bs e,
        Env.refines (@EqSt _) H1 H2 ->
        anon_sem_exp H1 bs e ->
        anon_sem_exp H2 bs e.
    Proof.
      induction e using exp_ind2; intros * Href Hsem; inv Hsem; eauto;
        econstructor;
        try (solve [rewrite Forall_forall in *; intros; eauto]).
      - (* merge *)
        rewrite Forall_forall in *; intros * Hin.
        specialize (H _ Hin). specialize (H3 _ Hin).
        rewrite Forall_forall in *; intros; eauto.
      - (* case *)
        rewrite Forall_forall in *; intros * Hin * Heq; subst.
        specialize (H _ Hin). specialize (H8 _ Hin _ eq_refl). simpl in *.
        rewrite Forall_forall in *; eauto.
      - (* app *)
        destruct H9 as (?&?&?&?&Hes&Her&Hbools&Hnode&Happ).
        do 4 eexists. repeat split; eauto.
        + eapply Forall2_impl_In; [|eauto]; intros.
          eapply sem_exp_refines; eauto.
        + eapply Forall2_impl_In; [|eauto]; intros.
          eapply sem_exp_refines; eauto.
        + eapply anon_app_refines; eauto.
    Qed.
    Hint Resolve anon_sem_exp_refines.

    Hint Resolve Env.union_refines2 Env.union_dom Env.adds_opt'_refines Env.adds_opt'_dom
         EqStrel EqStrel_Reflexive.

    Definition anons (env : list (type * nclock)) : list (option ident) :=
      List.map (fun '(_, (_, o)) => o) env.

    Fact anons_anon_streams : forall anns,
        map_filter id (anons anns) = map fst (Syn.anon_streams anns).
    Proof.
      induction anns; simpl; auto.
      destruct a as (?&?&[?|]); simpl; auto.
      f_equal; auto.
    Qed.

    Fact anons_In : forall x anns,
        In (Some x) (anons anns) ->
        In x (map fst (Syn.anon_streams anns)).
    Proof.
      induction anns; intros Hin; simpl in *; inv Hin;
        destruct a as (?&?&?); subst.
      - left; auto.
      - destruct o; simpl; auto.
    Qed.

    Fact anons_NoDup : forall anns,
      NoDup (map fst (Syn.anon_streams anns)) ->
      NoDupo (anons anns).
    Proof.
      induction anns; intros Hnd; simpl in *.
      - constructor.
      - destruct a as (?&?&?).
        destruct o; constructor; auto; inv Hnd; auto.
        intro contra. apply H1.
        rewrite Ino_In in contra. apply anons_In; auto.
    Qed.

    Hint Constructors anon_sem_exp.

    Fact sem_exps_fresh1 : forall env H b es vs,
      Forall
        (fun e => forall vs,
            Env.dom H (map fst env) ->
            NoDupMembers (env ++ fresh_in e) ->
            wl_exp G e ->
            Sem.sem_exp G H b e vs ->
            exists H',
              Env.refines (@EqSt _) H H' /\ Env.dom H' (map fst env ++ map fst (fresh_in e)) /\
              anon_sem_exp H' b e) es ->
      Env.dom H (map fst env) ->
      NoDupMembers (env ++ fresh_ins es) ->
      Forall (wl_exp G) es ->
      Forall2 (Sem.sem_exp G H b) es vs ->
      exists H', Env.refines (@EqSt _) H H' /\
            Env.dom H' (map fst env ++ map fst (fresh_ins es)) /\
            Forall (anon_sem_exp H' b) es.
    Proof.
      induction es; intros * Hf Hdom Hnd Hwl Hsem;
        inv Hwl; inv Hsem; inv Hf.
      - simpl_ndup Hnd. exists H; auto.
      - unfold fresh_ins in Hnd; simpl_ndup Hnd.
        eapply IHes in H7 as (H'2&Hr2&Hd2&Hs2); eauto. 2:ndup_r Hnd. clear IHes.
        eapply H5 in H4 as (H'1&Hr1&Hd1&Hs1); eauto. 2:ndup_l Hnd. clear H5.
        exists (Env.union H'1 H'2). repeat split; auto.
        apply NoDupMembers_app_r, fst_NoDupMembers in Hnd. rewrite map_app in Hnd.
        constructor; eauto. 2:eapply Forall_impl; [|eauto]; intros.
        1,2:eapply anon_sem_exp_refines. 2,4:eauto.
        eapply Env.union_refines3 in Hdom; eauto.
        eapply Env.union_refines4 in Hdom; eauto.
    Qed.

    Corollary sem_exps_fresh2 : forall env H b es vs,
        Forall
          (Forall
            (fun e => forall vs,
                  Env.dom H (map fst env) ->
                  NoDupMembers (env ++ fresh_in e) ->
                  wl_exp G e ->
                  Sem.sem_exp G H b e vs ->
                  exists H',
                    Env.refines (@EqSt _) H H' /\ Env.dom H' (map fst env ++ map fst (fresh_in e)) /\
                    anon_sem_exp H' b e)) es ->
        Env.dom H (map fst env) ->
        NoDupMembers (env ++ flat_map fresh_ins es) ->
        Forall (Forall (wl_exp G)) es ->
        Forall2 (Forall2 (Sem.sem_exp G H b)) es vs ->
        exists H',
          Env.refines (@EqSt _) H H' /\
          Env.dom H' (map fst env ++ map fst (flat_map fresh_ins es)) /\
          Forall (Forall (anon_sem_exp H' b)) es.
    Proof.
      induction es; intros * Hf Hdom Hnd Hwl Hsem;
        inv Hwl; inv Hsem; inv Hf.
      - simpl_ndup Hnd. exists H; auto.
      - simpl_ndup Hnd.
        eapply IHes in H7 as (H'2&Hr2&Hd2&Hs2); eauto. 2:ndup_r Hnd. clear IHes.
        eapply sem_exps_fresh1 in H5 as (H'1&Hr1&Hd1&Hs1); eauto. 2:ndup_l Hnd.
        exists (Env.union H'1 H'2). repeat split; auto.
        apply NoDupMembers_app_r, fst_NoDupMembers in Hnd. rewrite map_app in Hnd.
        constructor; auto.
        2:eapply Forall_impl; [|eauto]; intros.
        1,2:eapply Forall_impl; [|eauto]; intros.
        1,2:eapply anon_sem_exp_refines. 2,4:eauto.
        eapply Env.union_refines3 in Hdom; eauto.
        eapply Env.union_refines4 in Hdom; eauto.
    Qed.

    Corollary sem_exps_fresh3: forall env H b brs vs,
        Forall
          (LiftO True
            (Forall
                (fun e => forall vs,
                    Env.dom H (map fst env) ->
                    NoDupMembers (env ++ fresh_in e) ->
                    wl_exp G e ->
                    Sem.sem_exp G H b e vs ->
                    exists H',
                      Env.refines (@EqSt _) H H' /\
                      Env.dom H' (map fst env ++ map fst (fresh_in e)) /\
                      anon_sem_exp H' b e))) brs ->
        NoDupMembers (env ++ flat_map (or_default_with [] fresh_ins) brs) ->
        Env.dom H (map fst env) ->
        (forall es, In (Some es) brs -> Forall (wl_exp G) es) ->
        Forall2 (fun oes vs => forall es, oes = Some es -> Forall2 (Sem.sem_exp G H b) es vs) brs vs ->
        exists H',
          Env.refines (@EqSt _) H H' /\
          Env.dom H' (map fst env ++ map fst (flat_map (or_default_with [] fresh_ins) brs)) /\
          Forall (fun oes => forall es, oes = Some es -> Forall (anon_sem_exp H' b) es) brs.
    Proof.
      induction brs; intros * Hf Hnd Hdom Hwl Hsem; inv Hsem; inv Hf.
      - simpl_ndup Hnd. exists H. auto.
      - simpl_ndup Hnd.
        eapply IHbrs in H5 as (H'2&Hr2&Hd2&Hs2); eauto. 2:ndup_r Hnd. clear IHbrs.
        destruct a; simpl in *.
        + eapply sem_exps_fresh1 in H3 as (H'1&Hr1&Hd1&Hs1); eauto. 2:ndup_l Hnd.
          exists (Env.union H'1 H'2). repeat split; auto.
          apply NoDupMembers_app_r, fst_NoDupMembers in Hnd. rewrite map_app in Hnd.
          constructor; auto. intros ? Heq; inv Heq.
          2:eapply Forall_impl; [|eauto]; intros.
          1,2:eapply Forall_impl; [|eauto]; intros.
          1,2:eapply anon_sem_exp_refines. 2,4:eauto.
          eapply Env.union_refines3 in Hdom; eauto.
          eapply Env.union_refines4 in Hdom; eauto.
        + exists H'2. repeat split; auto.
          constructor; auto. intros ? Heq. inv Heq.
    Qed.

    Lemma sem_exp_fresh : forall env H b e vs,
        Env.dom H (map fst env) ->
        NoDupMembers (env ++ fresh_in e) ->
        wl_exp G e ->
        Sem.sem_exp G H b e vs ->
        exists H', Env.refines (@EqSt _) H H' /\
              Env.dom H' (map fst env ++ map fst (fresh_in e)) /\
              anon_sem_exp H' b e.
    Proof.
      induction e using exp_ind2;
        intros * Hdom Hnd Hwl Hsem;
        inv Hwl; inv Hsem; simpl_ndup Hnd.
      - (* const *) exists H; auto.
      - (* enum *) exists H; auto.
      - (* var *) exists H; auto.
      - (* unop *)
        eapply IHe in H8 as (?&?&?&?); eauto.
      - (* binop *)
        eapply IHe1 in H9 as (H'1&Href1&Hdom1&?); eauto. 2:ndup_l Hnd.
        eapply IHe2 in H12 as (H'2&Href2&Hdom2&?); eauto. 2:ndup_r Hnd.
        exists (Env.union H'1 H'2). repeat split; auto.
        apply NoDupMembers_app_r, fst_NoDupMembers in Hnd.
        rewrite map_app in Hnd.
        econstructor; eauto.
        1,2:eapply anon_sem_exp_refines; [|eauto].
        eapply Env.union_refines3 in Hdom; eauto.
        eapply Env.union_refines4 in Hdom; eauto.
      - (* fby *)
        eapply sem_exps_fresh1 in H0 as (H'0&Hr0&Hd0&Hs0); eauto. 2:ndup_l Hnd.
        eapply sem_exps_fresh1 in H1 as (H'1&Hr1&Hd1&Hs1); eauto. 2:ndup_r Hnd; ndup_l Hnd.
        exists (Env.union H'0 H'1). repeat split; auto 10.
        apply NoDupMembers_app_r, fst_NoDupMembers in Hnd.
        repeat rewrite map_app in Hnd.
        econstructor; eauto.
        1-2:eapply Forall_impl; [|eauto]; simpl; intros; eapply anon_sem_exp_refines; [|eauto].
        eapply Env.union_refines3 with (m:=H). 1-8:eauto.
        eapply Env.union_refines4 with (m:=H). 1-8:eauto.
      - (* arrow *)
        eapply sem_exps_fresh1 in H0 as (H'0&Hr0&Hd0&Hs0); eauto. 2:ndup_l Hnd.
        eapply sem_exps_fresh1 in H1 as (H'1&Hr1&Hd1&Hs1); eauto. 2:ndup_r Hnd; ndup_l Hnd.
        exists (Env.union H'0 H'1). repeat split; auto 10.
        apply NoDupMembers_app_r, fst_NoDupMembers in Hnd.
        repeat rewrite map_app in Hnd.
        econstructor; eauto.
        1-2:eapply Forall_impl; [|eauto]; simpl; intros; eapply anon_sem_exp_refines; [|eauto].
        eapply Env.union_refines3 with (m:=H). 1-8:eauto.
        eapply Env.union_refines4 with (m:=H). 1-8:eauto.
      - (* when *)
        eapply sem_exps_fresh1 in H0 as (H'1&Hr1&Hd1&Hs1); eauto.
      - (* merge *)
        eapply sem_exps_fresh2 in H0 as (H'1&Hr1&Hd1&Hs1); eauto.
      - (* case *)
        eapply IHe in H14 as (H'0&Hr0&Hd0&Hsd0); eauto. 2:do 2 ndup_l Hnd.
        eapply sem_exps_fresh3 in H0 as (H'1&Hr1&Hd1&Hs1); eauto. 2:ndup_r Hnd; ndup_l Hnd.
        eapply sem_exps_fresh1 in H20 as (H'2&Hr2&Hd2&Hsd2); eauto. 2:do 2 ndup_r Hnd.
        exists (Env.union H'0 (Env.union H'1 H'2)); repeat split; auto.
        econstructor; eauto.
        2:clear H17 H19; do 2 (eapply Forall_impl; [|eauto]; intros; subst).
        3:eapply Forall_impl; [|eauto]; intros; subst.
        1-3:eapply anon_sem_exp_refines; [|eauto].
        eapply Env.union_refines3 in Hdom; eauto.
        2:etransitivity; [eapply Env.union_refines3 in Hdom; eauto|eapply Env.union_refines4 in Hdom; eauto].
        4:etransitivity; [|eapply Env.union_refines4 in Hdom; eauto]; [eapply Env.union_refines4 in Hdom; eauto|].
        1,3,5:(eapply NoDupMembers_app_r in Hnd;
              repeat rewrite <-map_app; rewrite <-fst_NoDupMembers; auto).
        1,2:(eapply NoDupMembers_app_r, NoDupMembers_app_r in Hnd;
            repeat rewrite <-map_app; rewrite <-fst_NoDupMembers; auto).
      - (* app *)
        eapply sem_exps_fresh1 in H0 as (H'0&Hr0&Hd0&Hs0); eauto. 2:ndup_l Hnd.
        eapply sem_exps_fresh1 in H1 as (H'1&Hr1&Hd1&Hs1); eauto. 2:ndup_r Hnd; ndup_l Hnd.
        2:eapply Forall2_map_2; eapply H17.
        assert (length vs = length a) as Hlen.
        { specialize (H19 0). inv H19. rewrite H1 in H10; inv H10.
          apply Forall2_length in H3. unfold idents in H3. repeat rewrite map_length in H3.
          congruence. }
        remember (Env.adds_opt' (anons a) vs (Env.union H'0 H'1)) as H'3.
        rewrite fst_NoDupMembers in Hnd. repeat rewrite map_app in Hnd.
        assert (Env.refines (@EqSt _) (Env.union H'0 H'1) H'3) as Hr3.
        { subst. eapply refines_eq_EqSt, Env.adds_opt'_refines.
          + unfold anons. rewrite map_length; auto.
          + repeat rewrite app_assoc in Hnd. rewrite (Permutation_app_comm _ (map fst (Syn.anon_streams a))) in Hnd.
            repeat rewrite <- app_assoc in Hnd.
            eapply Forall_forall; intros; subst.
            eapply anons_In in H0. eapply NoDup_app_In in Hnd; eauto.
            erewrite Env.dom_use; eauto.
        }
        assert (Env.refines (@EqSt _) H H'3) as Hr4.
        { etransitivity; [|eauto]. eauto. }
        exists H'3. repeat split; auto.
        + rewrite HeqH'3, <- anons_anon_streams, app_assoc, app_assoc.
          eapply Env.adds_opt'_dom; eauto.
          unfold anons. rewrite map_length; auto.
          repeat rewrite <- app_assoc. eauto.
        + econstructor; eauto.
          * eapply Forall_impl_In; [|eauto]; intros.
            eapply anon_sem_exp_refines; [|eauto]. etransitivity; [|eapply Hr3].
            eapply Env.union_refines3 in Hd1; eauto.
            apply NoDup_app_r in Hnd. rewrite app_assoc in Hnd. apply NoDup_app_l in Hnd; auto.
          * eapply Forall_impl_In; [|eauto]; intros; simpl in *.
            eapply anon_sem_exp_refines; [|eauto]. etransitivity; [|eapply Hr3].
            eapply Env.union_refines4 in Hd1; eauto.
            apply NoDup_app_r in Hnd. rewrite app_assoc in Hnd. apply NoDup_app_l in Hnd; auto.
          * assert (Forall2 (fun o v => forall x, o = Some x -> Env.find x H'3 = Some v) (anons a) vs) as Hvs.
            { eapply all_In_Forall2; eauto. unfold anons; rewrite map_length; auto.
              intros ? ? Hin ? ?; subst.
              eapply Env.In_find_adds_opt'; eauto.
              eapply anons_NoDup, NoDup_app_r, NoDup_app_r, NoDup_app_r; eauto. }
            do 4 esplit. repeat split; eauto.
            -- eapply Forall2_impl_In; [|eauto]; intros. eapply sem_exp_refines; eauto.
            -- eapply Forall2_impl_In; [|eauto]; intros. eapply sem_exp_refines; eauto.
            -- clear - Hvs.
               unfold anons in Hvs. rewrite Forall2_map_1 in Hvs.
               induction Hvs; intros; constructor; auto.
               destruct x as (?&?&?). destruct o; simpl; auto.
               econstructor. eapply H. 1,2:reflexivity.
    Qed.

    Lemma sem_exp_anon : forall env H b e vs,
        Env.dom H (map fst env) ->
        NoDupMembers (env ++ anon_in e) ->
        Forall2 (fun '(_, (_, o)) s => LiftO True (fun x : ident => sem_var H x s) o) (annot e) vs ->
        wl_exp G e ->
        Sem.sem_exp G H b e vs ->
        exists H', Env.refines (@EqSt _) H H' /\
          Env.dom H' (map fst env ++ map fst (anon_in e)) /\
          anon_sem_exp H' b e.
    Proof.
      intros * Hdom Hndup Hf Hwl Hsem.
      destruct e; simpl in *.
      1-10:eapply sem_exp_fresh in Hsem as (H'&?&?&?); simpl in *; eauto.
      (* app *)
      inv Hwl; inv Hsem.
      assert (Hsem0:=H13). eapply sem_exps_fresh1 in H13 as (H'1&Hr1&?&?); eauto. 3:ndup_l Hndup.
      2:{ eapply Forall_forall; intros * Hin ?????.
          eapply sem_exp_fresh; eauto. }
      assert (Hsem1:=H15). eapply Forall2_map_2 in H15.
      eapply sem_exps_fresh1 in H15 as (H'2&Hr2&?&?); eauto. 3:ndup_r Hndup.
      2:{ eapply Forall_forall; intros * Hin ?????.
          eapply sem_exp_fresh; eauto. }
      assert (Env.dom (Env.union H'1 H'2) (map fst env0 ++ map fst (fresh_ins l) ++ map fst (fresh_ins l0))) as Hd3 by eauto.
      exists (Env.union H'1 H'2). repeat split; auto.
      - repeat rewrite map_app. eauto.
      - rewrite fst_NoDupMembers, map_app, map_app in Hndup.
        econstructor; eauto.
        + eapply Forall_impl; [|eauto]. intros.
          eapply anon_sem_exp_refines; [|eauto].
          eapply Env.union_refines3 in H2; eauto. apply NoDup_app_r in Hndup; auto.
        + eapply Forall_impl; [|eapply H3]; simpl in *. intros.
          eapply anon_sem_exp_refines; [|eauto].
          eapply Env.union_refines4 in H2; eauto. apply NoDup_app_r in Hndup; auto.
        + do 4 esplit. repeat split; eauto.
            -- eapply Forall2_impl_In; [|eauto]; intros. eapply sem_exp_refines; [|eauto]; eauto.
            -- eapply Forall2_impl_In; [|eauto]; intros. simpl in *.
               eapply sem_exp_refines; [|eauto]; eauto.
            -- eapply anon_app_refines. 2-4:eauto. eauto.
    Qed.

    Corollary sem_exps_anon : forall env H b es vs,
        Env.dom H (map fst env) ->
        NoDupMembers (env ++ anon_ins es) ->
        Forall2 (fun '(_, (_, o)) s => LiftO True (fun x : ident => sem_var H x s) o) (annots es) (concat vs) ->
        Forall (wl_exp G) es ->
        Forall2 (Sem.sem_exp G H b) es vs ->
        exists H', Env.refines (@EqSt _) H H' /\
          Env.dom H' (map fst env ++ map fst (anon_ins es)) /\
          Forall (anon_sem_exp H' b) es.
    Proof.
      intros * Hdom Hnd Hvar Hwl Hsem.
      induction Hsem; simpl in *; inv Hwl.
      - exists H. repeat split; auto.
      - unfold anon_ins in *; simpl in *.
        apply Forall2_app_split in Hvar as (Hvar1&Hvar2).
        2:{ apply Forall2_length in Hvar. apply sem_exps_numstreams in Hsem; auto.
            repeat rewrite app_length in Hvar. rewrite Hsem in Hvar.
            rewrite <- Nat.add_cancel_r; eauto. }
        eapply IHHsem in Hvar2 as (H'2&?&?&?); eauto. 2:ndup_r Hnd. clear IHHsem.
        eapply sem_exp_anon in H0 as (H'1&?&?&?); eauto. 2:ndup_l Hnd.
        exists (Env.union H'1 H'2). repeat split; auto.
        + rewrite map_app; auto.
        + apply NoDupMembers_app_r, fst_NoDupMembers in Hnd. rewrite map_app in Hnd.
          constructor; auto.
          2:eapply Forall_impl; [|eauto]; intros.
          1,2:eapply anon_sem_exp_refines; [|eauto].
          eapply Env.union_refines3 in Hdom; eauto.
          eapply Env.union_refines4 in Hdom; eauto.
    Qed.

    Lemma sem_equation_anon : forall env H b equ,
        Env.dom H (map fst env) ->
        NoDupMembers (env ++ anon_in_eq equ) ->
        wc_equation G (idck env) equ ->
        Sem.sem_equation G H b equ ->
        exists H', Env.refines (@EqSt _) H H' /\
          Env.dom H' (map fst env ++ map fst (anon_in_eq equ)) /\
          anon_sem_equation H' b equ.
    Proof.
      intros ? ? ? (xs&es) Hdom Hnd Hwc Hsem.
      destruct Hwc as (Hwc1&Hwc2&_). inv Hsem.
      eapply sem_exps_anon in H5 as (H'&?&?&?); eauto.
      - clear - Hwc2 H6.
        rewrite Forall2_swap_args, nclocksof_annots, Forall2_map_1 in Hwc2.
        eapply Forall2_trans_ex in H6; [|eauto]. clear - H6.
        eapply Forall2_impl_In; eauto. intros (?&?&?) ??? (?&?&?&?).
        destruct o; simpl in *; subst; auto.
    Qed.

    (** Properties of sem_exp_anon *)

    Lemma sem_exp_anon_sem_var :
      forall env H b e vs,
        det_nodes G ->
        wc_exp G env e ->
        sem_exp G H b e vs ->
        anon_sem_exp H b e ->
        Forall2 (fun '(_, o) s => LiftO True (fun x : ident => sem_var H x s) o) (nclockof e) vs.
    Proof.
      intros * HdetG Hwc Hsem Hanon.
      assert (length vs = length (nclockof e)) as Hlen.
      { rewrite length_nclockof_numstreams. eapply sem_exp_numstreams; eauto. }
      inv Hwc; inv Hsem; inv Hanon; simpl in *.
      1-6:constructor; simpl; auto.
      - (* fby *)
        clear - Hlen H4. rewrite map_length in Hlen; symmetry in Hlen.
        eapply Forall2_ignore2' in H4; eauto.
        clear Hlen. induction H4; simpl; constructor; auto.
        destruct x as [? [? [?|]]]; simpl; auto. inv H0.
      - (* arrow *)
        clear - Hlen H4. rewrite map_length in Hlen; symmetry in Hlen.
        eapply Forall2_ignore2' in H4; eauto.
        clear Hlen. induction H4; simpl; constructor; auto.
        destruct x as [? [? [?|]]]; simpl; auto. inv H0.
      - (* when *)
        rewrite map_length in Hlen.
        rewrite Forall2_map_1; simpl. apply Forall2_forall2; split; auto.
      - (* merge *)
        rewrite map_length in Hlen.
        rewrite Forall2_map_1; simpl. apply Forall2_forall2; split; auto.
      - (* case *)
        rewrite map_length in Hlen.
        rewrite Forall2_map_1; simpl. apply Forall2_forall2; split; auto.
      - (* app *)
        destruct H12 as (?&?&?&?&Hsem'&Hsemr'&Hbools'&Hnode'&Happ).
        assert (EqSts x2 vs) as Heq.
        { eapply det_exps in H13; eauto.
          rewrite <-Forall2_map_2 in H15, Hsemr'.
          eapply det_exps in H15; eauto.
          repeat rewrite concat_map_singl1 in H15. rewrite <-H15 in H16.
          eapply bools_ofs_det in H16; eauto.
          eapply EqStN_EqSts. intros. eapply EqStNs_unmask; eauto.
          - eapply EqStN_EqSt; eauto.
          - intros k. specialize (H17 k). specialize (Hnode' k).
            eapply sem_node_morph in Hnode'. 2,4:reflexivity.
            2:{ eapply map_st_EqSt; eauto.
                intros ?? Heq. rewrite Heq, H16. reflexivity. }
            eapply EqStN_EqSts, det_nodes_ins; eauto. }
        eapply Forall2_trans_ex in Heq; [|eapply Happ].
        rewrite Forall2_map_1.
        eapply Forall2_impl_In; eauto. intros (?&?&?) ? _ _ (?&_&Hvar&Heqx); eauto; simpl.
        destruct o; simpl in *; auto. now rewrite <-Heqx.
    Qed.

    Corollary sem_exps_anon_sem_var :
      forall env H b es vs,
        det_nodes G ->
        Forall (wc_exp G env) es ->
        Forall2 (sem_exp G H b) es vs ->
        Forall (anon_sem_exp H b) es ->
        Forall2 (fun '(_, o) s => LiftO True (fun x : ident => sem_var H x s) o) (nclocksof es) (concat vs).
    Proof.
      induction es; intros * Hdet Hwc Hsem Hanon; inv Hwc; inv Hsem; inv Hanon; simpl; auto.
      apply Forall2_app; auto.
      eapply sem_exp_anon_sem_var; eauto.
    Qed.
  End AnonSemantics.

  (** ** Clocked semantics *)
  (** We add an alignment predicate to the node case of the semantics, which checks that
      every flow in the node is aligned with its clock.
      We also add this constraint for the anonymous outputs of a node.
      This forces us to constrain anonymous streams to appear in history.
      We also constrain the domain of the history to be closed, that is only
      contain the named and anonymous streams of the node.
   *)
  Section ClockedSemantics.
    Definition sc_var_inv env H bs :=
      Forall (fun '(x, ck) => exists xs, sem_var H x xs /\ sem_clock H bs ck (abstract_clock xs)) env.

    Definition clocked_node H bs (env : list (ident * (type * clock))) bcks :=
      Env.dom H (map fst (env ++ (flat_map anon_in_block) bcks)) /\
      sc_var_inv (idck env) H bs.

    Definition clocked_app H bs (lann: list (type * nclock)) vss :=
      Forall2 (fun '(_, (ck, o)) vs => LiftO True (fun x => sem_var H x vs /\
                                                   sem_clock H bs ck (abstract_clock vs)) o) lann vss.

    Lemma clocked_app_refines :
      Proper (Env.refines (EqSt (A:=svalue)) ==> eq ==> eq ==> eq ==> Basics.impl) clocked_app.
    Proof.
      unfold anon_app.
      intros ?????????????; subst.
      eapply Forall2_impl_In; [|eauto]. intros (?&?&[|]) ? _ _ ?; simpl in *; auto.
      destruct H0.
      split; eauto using sem_var_refines, sem_clock_refines.
    Qed.
    Hint Resolve clocked_app_refines.

    Context {prefs : PS.t}.
    Variable G : @global prefs.

    Inductive sem_exp_ck : history -> Stream bool -> exp -> list (Stream svalue) -> Prop :=
    | Sconst:
        forall H bs c cs,
          cs ≡ const bs c ->
          sem_exp_ck H bs (Econst c) [cs]

    | Senum:
        forall H b k ty es,
          es ≡ enum b k ->
          sem_exp_ck H b (Eenum k ty) [es]

    | Svar:
        forall H b x s ann,
          sem_var H x s ->
          sem_exp_ck H b (Evar x ann) [s]

    | Sunop:
        forall H b e op ty s o ann,
          sem_exp_ck H b e [s] ->
          typeof e = [ty] ->
          lift1 op ty s o ->
          sem_exp_ck H b (Eunop op e ann) [o]

    | Sbinop:
        forall H b e1 e2 op ty1 ty2 s1 s2 o ann,
          sem_exp_ck H b e1 [s1] ->
          sem_exp_ck H b e2 [s2] ->
          typeof e1 = [ty1] ->
          typeof e2 = [ty2] ->
          lift2 op ty1 ty2 s1 s2 o ->
          sem_exp_ck H b (Ebinop op e1 e2 ann) [o]

    | Sfby:
        forall H b e0s es anns s0ss sss os,
          Forall2 (sem_exp_ck H b) e0s s0ss ->
          Forall2 (sem_exp_ck H b) es sss ->
          Forall3 fby (concat s0ss) (concat sss) os ->
          sem_exp_ck H b (Efby e0s es anns) os

    | Sarrow:
        forall H b e0s es anns s0ss sss os,
          Forall2 (sem_exp_ck H b) e0s s0ss ->
          Forall2 (sem_exp_ck H b) es sss ->
          Forall3 arrow (concat s0ss) (concat sss) os ->
          sem_exp_ck H b (Earrow e0s es anns) os

    | Swhen:
        forall H b x s k es lann ss os,
          Forall2 (sem_exp_ck H b) es ss ->
          sem_var H x s ->
          Forall2 (fun s' => when k s' s) (concat ss) os ->
          sem_exp_ck H b (Ewhen es x k lann) os

    | Smerge:
        forall H b x tx s es lann vs os,
          sem_var H x s ->
          Forall2 (Forall2 (sem_exp_ck H b)) es vs ->
          Forall2Transpose (merge s) (List.map (@concat _) vs) os ->
          sem_exp_ck H b (Emerge (x, tx) es lann) os

    | Scase:
        forall H b e s es d lann vs vd os,
          sem_exp_ck H b e [s] ->
          Forall2 (fun oes vs => forall es, oes = Some es -> Forall2 (sem_exp_ck H b) es vs) es vs ->
          Forall2 (fun oes vs => oes = None -> Forall2 EqSts vs vd) es vs ->
          Forall2 (sem_exp_ck H b) d vd ->
          Forall2Transpose (case s) (List.map (@concat _) vs) os ->
          sem_exp_ck H b (Ecase e es d lann) os

    | Sapp:
        forall H b f es er lann ss os rs bs,
          Forall2 (sem_exp_ck H b) es ss ->
          Forall2 (fun e r => sem_exp_ck H b e [r]) er rs ->
          bools_ofs rs bs ->
          (forall k, sem_node_ck f (List.map (maskv k bs) (concat ss)) (List.map (maskv k bs) os)) ->
          clocked_app H b lann os ->
          sem_exp_ck H b (Eapp f es er lann) os

    with sem_equation_ck: history -> Stream bool -> equation -> Prop :=
      Seq:
        forall H b xs es ss,
          Forall2 (sem_exp_ck H b) es ss ->
          Forall2 (sem_var H) xs (concat ss) ->
          sem_equation_ck H b (xs, es)

    with sem_block_ck: history -> Stream bool -> block -> Prop :=
      | Sdeq:
          forall H b eq,
            sem_equation_ck H b eq ->
            sem_block_ck H b (Beq eq)
      | Sreset:
          forall H b blocks er sr r,
            sem_exp_ck H b er [sr] ->
            bools_of sr r ->
            (forall k, Forall (sem_block_ck (mask_hist k r H) (maskb k r b)) blocks) ->
            sem_block_ck H b (Breset blocks er)

    with sem_node_ck: ident -> list (Stream svalue) -> list (Stream svalue) -> Prop :=
      Snode:
        forall f ss os n H b,
          find_node f G = Some n ->
          Forall2 (sem_var H) (idents n.(n_in)) ss ->
          Forall2 (sem_var H) (idents n.(n_out)) os ->
          Forall (sem_block_ck H b) n.(n_blocks) ->
          b = clocks_of ss ->
          clocked_node H b (n.(n_in) ++ n.(n_vars) ++ n.(n_out)) n.(n_blocks) ->
          sem_node_ck f ss os.

    Hint Constructors sem_exp sem_equation.

    (** Custom induction schemes *)

    Section sem_exp_ind2.
      Variable P_exp : history -> Stream bool -> exp -> list (Stream svalue) -> Prop.
      Variable P_equation : history -> Stream bool -> equation -> Prop.
      Variable P_block : history -> Stream bool -> block -> Prop.
      Variable P_node : ident -> list (Stream svalue) -> list (Stream svalue) -> Prop.

      Hypothesis ConstCase:
        forall H b c cs,
          cs ≡ const b c ->
          P_exp H b (Econst c) [cs].

      Hypothesis EnumCase:
        forall H b k ty es,
          es ≡ enum b k ->
          P_exp H b (Eenum k ty) [es].

      Hypothesis VarCase:
        forall H b x s ann,
          sem_var H x s ->
          P_exp H b (Evar x ann) [s].

      Hypothesis UnopCase:
        forall H b e op ty s o ann,
          sem_exp_ck H b e [s] ->
          P_exp H b e [s] ->
          typeof e = [ty] ->
          lift1 op ty s o ->
          P_exp H b (Eunop op e ann) [o].

      Hypothesis BinopCase:
        forall H b e1 e2 op ty1 ty2 s1 s2 o ann,
          sem_exp_ck H b e1 [s1] ->
          P_exp H b e1 [s1] ->
          sem_exp_ck H b e2 [s2] ->
          P_exp H b e2 [s2] ->
          typeof e1 = [ty1] ->
          typeof e2 = [ty2] ->
          lift2 op ty1 ty2 s1 s2 o ->
          P_exp H b (Ebinop op e1 e2 ann) [o].

      Hypothesis FbyCase:
        forall H b e0s es anns s0ss sss os,
          Forall2 (sem_exp_ck H b) e0s s0ss ->
          Forall2 (P_exp H b) e0s s0ss ->
          Forall2 (sem_exp_ck H b) es sss ->
          Forall2 (P_exp H b) es sss ->
          Forall3 fby (concat s0ss) (concat sss) os ->
          P_exp H b (Efby e0s es anns) os.

      Hypothesis ArrowCase:
        forall H b e0s es anns s0ss sss os,
          Forall2 (sem_exp_ck H b) e0s s0ss ->
          Forall2 (P_exp H b) e0s s0ss ->
          Forall2 (sem_exp_ck H b) es sss ->
          Forall2 (P_exp H b) es sss ->
          Forall3 arrow (concat s0ss) (concat sss) os ->
          P_exp H b (Earrow e0s es anns) os.

      Hypothesis WhenCase:
        forall H b x s k es lann ss os,
          Forall2 (sem_exp_ck H b) es ss ->
          Forall2 (P_exp H b) es ss ->
          sem_var H x s ->
          Forall2 (fun s' => when k s' s) (concat ss) os ->
          P_exp H b (Ewhen es x k lann) os.

      Hypothesis MergeCase:
        forall H b x tx s es lann vs os,
          sem_var H x s ->
          Forall2 (Forall2 (sem_exp_ck H b)) es vs ->
          Forall2 (Forall2 (P_exp H b)) es vs ->
          Forall2Transpose (merge s) (List.map (@concat _) vs) os ->
          P_exp H b (Emerge (x, tx) es lann) os.

      Hypothesis CaseCase:
        forall H b e s es d lann vs vd os,
          sem_exp_ck H b e [s] ->
          P_exp H b e [s] ->
          Forall2 (fun oes vs => forall es, oes = Some es -> Forall2 (sem_exp_ck H b) es vs) es vs ->
          Forall2 (fun oes vs => forall es, oes = Some es -> Forall2 (P_exp H b) es vs) es vs ->
          Forall2 (fun oes vs => oes = None -> Forall2 EqSts vs vd) es vs ->
          Forall2 (sem_exp_ck H b) d vd ->
          Forall2 (P_exp H b) d vd ->
          Forall2Transpose (case s) (List.map (@concat _) vs) os ->
          P_exp H b (Ecase e es d lann) os.

      Hypothesis AppCase:
        forall H b f es er lann ss os sr bs,
          Forall2 (sem_exp_ck H b) es ss ->
          Forall2 (P_exp H b) es ss ->
          Forall2 (fun e r => sem_exp_ck H b e [r]) er sr ->
          Forall2 (fun e r => P_exp H b e [r]) er sr ->
          bools_ofs sr bs ->
          (forall k, sem_node_ck f (List.map (maskv k bs) (concat ss)) (List.map (maskv k bs) os)
                /\ P_node f (List.map (maskv k bs) (concat ss)) (List.map (maskv k bs) os)) ->
          clocked_app H b lann os ->
          P_exp H b (Eapp f es er lann) os.

      Hypothesis Equation:
        forall H b xs es ss,
          Forall2 (sem_exp_ck H b) es ss ->
          Forall2 (P_exp H b) es ss ->
          Forall2 (sem_var H) xs (concat ss) ->
          P_equation H b (xs, es).

      Hypothesis BeqCase:
        forall H b eq,
          sem_equation_ck H b eq ->
          P_equation H b eq ->
          P_block H b (Beq eq).

      Hypothesis BresetCase:
        forall H b blocks er sr r,
          sem_exp_ck H b er [sr] ->
          P_exp H b er [sr] ->
          bools_of sr r ->
          (forall k, Forall (sem_block_ck (mask_hist k r H) (maskb k r b)) blocks /\
                Forall (P_block (mask_hist k r H) (maskb k r b)) blocks) ->
          P_block H b (Breset blocks er).

      Hypothesis Node:
        forall f ss os n H b,
          find_node f G = Some n ->
          Forall2 (sem_var H) (idents n.(n_in)) ss ->
          Forall2 (sem_var H) (idents n.(n_out)) os ->
          Forall (sem_block_ck H b) n.(n_blocks) ->
          Forall (P_block H b) n.(n_blocks) ->
          b = clocks_of ss ->
          clocked_node H b (n.(n_in) ++ n.(n_vars) ++ n.(n_out)) n.(n_blocks) ->
          P_node f ss os.

      Local Ltac SolveForall :=
        match goal with
        | H: Forall ?P1 ?l |- Forall ?P2 ?l =>
          induction H; eauto
        | H: Forall2 ?P1 ?l1 ?l2 |- Forall2 ?P2 ?l1 ?l2 =>
          induction H; eauto
        | _ => idtac
        end.

      Fixpoint sem_exp_ck_ind2
               (H: history) (b: Stream bool) (e: exp) (ss: list (Stream svalue))
               (Sem: sem_exp_ck H b e ss)
               {struct Sem}
        : P_exp H b e ss
      with sem_equation_ck_ind2
             (H: history) (b: Stream bool) (e: equation)
             (Sem: sem_equation_ck H b e)
             {struct Sem}
           : P_equation H b e
      with sem_block_ck_ind2
             (H: history) (b: Stream bool) (d: block)
             (Sem: sem_block_ck H b d)
             {struct Sem}
           : P_block H b d
      with sem_node_ck_ind2
             (f: ident) (ss os: list (Stream svalue))
             (Sem: sem_node_ck f ss os)
             {struct Sem}
           : P_node f ss os.
      Proof.
        - inv Sem.
          + apply ConstCase; eauto.
          + apply EnumCase; eauto.
          + apply VarCase; auto.
          + eapply UnopCase; eauto.
          + eapply BinopCase; eauto.
          + eapply FbyCase; eauto; clear H3; SolveForall.
          + eapply ArrowCase; eauto; clear H3; SolveForall.
          + eapply WhenCase; eauto; clear H3; SolveForall.
          + eapply MergeCase; eauto; clear H3; SolveForall.
            constructor; auto. SolveForall.
          + eapply CaseCase; eauto.
            * clear - sem_exp_ck_ind2 H2.
              SolveForall. constructor; auto.
              intros; subst. specialize (H0 _ eq_refl). SolveForall.
            * clear - sem_exp_ck_ind2 H4.
              SolveForall.
          + eapply AppCase; eauto; clear H3 H4; SolveForall.
        - inv Sem.
          eapply Equation with (ss:=ss); eauto; clear H2; SolveForall.
        - inv Sem.
          + eapply BeqCase; eauto.
          + eapply BresetCase; eauto.
            intros k. specialize (H3 k). split; eauto. SolveForall.
        - inv Sem.
          eapply Node; eauto.
          clear H5. SolveForall.
      Qed.

    End sem_exp_ind2.

    Section sem_refines.

      Fact sem_exp_refines : forall b e H H' v,
        Env.refines (@EqSt _) H H' ->
        sem_exp_ck H b e v ->
        sem_exp_ck H' b e v.
      Proof with eauto.
        induction e using exp_ind2; intros Hi Hi' v Href Hsem; inv Hsem.
        - (* const *) constructor...
        - (* enum *) constructor...
        - (* var *)
          constructor. eapply sem_var_refines...
        - (* unop *) econstructor...
        - (* binop *) econstructor...
        - (* fby *)
          econstructor; eauto; repeat rewrite_Forall_forall...
        - (* arrow *)
          econstructor; eauto; repeat rewrite_Forall_forall...
        - (* when *)
          econstructor; eauto; repeat rewrite_Forall_forall...
          eapply sem_var_refines...
        - (* merge *)
          econstructor; eauto.
          + eapply sem_var_refines...
          + do 2 (eapply Forall2_impl_In; [|eauto]; intros).
            do 2 (eapply Forall_forall in H; [|eauto]); eauto.
        - (* case *)
          econstructor; eauto.
          + clear H11. do 2 (eapply Forall2_impl_In; [|eauto]; intros; subst).
            do 2 (eapply Forall_forall in H; [|eauto]); eauto.
          + eapply Forall2_impl_In; [|eauto]; intros.
            eapply Forall_forall in H0; eauto.
        - (* app *)
          econstructor; eauto. 1,2:repeat rewrite_Forall_forall...
          eapply clocked_app_refines; eauto.
      Qed.

      Fact sem_equation_refines : forall H H' b equ,
          Env.refines (@EqSt _) H H' ->
          sem_equation_ck H b equ ->
          sem_equation_ck H' b equ.
      Proof with eauto.
        intros * Href Hsem.
        destruct Hsem.
        econstructor.
        + eapply Forall2_impl_In; [| eauto].
          intros. eapply sem_exp_refines...
        + eapply Forall2_impl_In; [| eauto].
          intros. eapply sem_var_refines...
      Qed.

      Lemma sem_block_refines : forall bck H H' bs,
          Env.refines (@EqSt _) H H' ->
          sem_block_ck H bs bck ->
          sem_block_ck H' bs bck.
      Proof.
        induction bck using block_ind2; intros * Href Hsem;
          inv Hsem.
        - (* eq *)
          constructor; eauto using sem_equation_refines.
        - (* reset *)
          econstructor; eauto using sem_exp_refines.
          intros k. specialize (H8 k).
          eapply Forall_impl_In; [|eauto]. intros ?? Hsem.
          eapply Forall_forall in H; eauto.
          eapply H; [|eauto]; eauto using refines_mask.
      Qed.

    End sem_refines.

    Hint Constructors Sem.sem_exp Sem.sem_equation Sem.sem_block.

    Lemma sem_exp_ck_sem_exp : forall H b e vs,
        sem_exp_ck H b e vs ->
        sem_exp G H b e vs.
    Proof.
      intros * Hsem.
      eapply sem_exp_ck_ind2
        with (P_exp := Sem.sem_exp G)
             (P_equation := Sem.sem_equation G)
             (P_block := Sem.sem_block G)
             (P_node := Sem.sem_node G); intros; eauto.
      - (* app *)
        econstructor; eauto.
        intros k. specialize (H6 k) as (_&?); auto.
      - (* block *)
        econstructor; eauto.
        intros k. specialize (H4 k) as (_&?); auto.
      - (* node *)
        econstructor; eauto.
    Qed.

    Corollary sem_exps_ck_sem_exps : forall H b es vs,
        Forall2 (sem_exp_ck H b) es vs ->
        Forall2 (sem_exp G H b) es vs.
    Proof.
      intros * Hsem.
      eapply Forall2_impl_In; [|eauto]; intros.
      eapply sem_exp_ck_sem_exp; eauto.
    Qed.

    Lemma sem_node_ck_sem_node : forall f ins outs,
        sem_node_ck f ins outs ->
        sem_node G f ins outs.
    Proof.
      intros * Hsem.
      eapply sem_node_ck_ind2
        with (P_exp := Sem.sem_exp G)
             (P_equation := Sem.sem_equation G)
             (P_block := Sem.sem_block G)
             (P_node := Sem.sem_node G); intros; eauto.
      - (* app *)
        econstructor; eauto.
        intros k. specialize (H5 k) as (_&?); auto.
      - (* block *)
        econstructor; eauto.
        intros k. specialize (H3 k) as (_&?); auto.
      - (* node *)
        econstructor; eauto.
    Qed.

  End ClockedSemantics.

  (** Morphism properties *)

  Hint Constructors sem_exp.

  Add Parametric Morphism env : (sc_var_inv env)
      with signature Env.Equiv (@EqSt _) ==> @EqSt bool ==> Basics.impl
        as sc_var_inv_morph.
  Proof.
    intros ?? Heq1 ?? Heq2 Hinv.
    eapply Forall_impl; [|eauto]; intros (?&?) (xs&Hvar&Hck).
    exists xs. split.
    - rewrite <-Heq1; auto.
    - rewrite <-Heq1, <-Heq2; auto.
  Qed.

  Add Parametric Morphism : clocked_app
      with signature Env.Equiv (@EqSt _) ==> @EqSt _ ==> eq ==> @EqSts _ ==> Basics.impl
        as clocked_app_morph.
  Proof.
    intros H H' EH bs bs' Hb ? xs xs' Exs Hck.
    eapply Forall2_trans_ex in Exs; eauto.
    eapply Forall2_impl_In; [|eauto]; intros (?&?&?) ? _ _ (?&Hin&?&Heq).
    destruct o; simpl in *; auto. destruct H0.
    split.
    - now rewrite <-EH, <-Heq.
    - now rewrite <-EH, <-Hb, <-Heq.
  Qed.

  Add Parametric Morphism : clocked_node
      with signature eq ==> @EqSt _ ==> eq ==> eq ==> Basics.impl
        as clocked_node_morph.
  Proof.
    intros H bs bs' Hb ?? (Hdom&Hsc).
    split; auto.
    rewrite <-Hb; auto.
  Qed.

  Hint Resolve clocked_app_morph_Proper clocked_node_morph_Proper.

  Add Parametric Morphism {prefs} (G : @global prefs) : (sem_exp_ck G)
      with signature Env.Equiv (@EqSt _) ==> @EqSt bool ==> eq ==> @EqSts svalue ==> Basics.impl
        as sem_exp_ck_morph.
  Proof.
    intros H H' EH b b' Eb e xs xs' Exs Hsem. revert H' b' xs' EH Eb Exs.
    eapply sem_exp_ck_ind2 with
        (P_exp := fun H b e xs => forall H' b' xs', Env.Equiv (@EqSt _) H H' -> b ≡ b' -> EqSts xs xs' -> sem_exp_ck G H' b' e xs')
        (P_equation := fun H b e => True)
        (P_block := fun H b d => True)
        (P_node := fun f xs ys => forall ys', EqSts ys ys' -> sem_node_ck G f xs ys');
      intros; eauto; take (EqSts _ _) and rename it into Exs.
    - inv Exs; take (Forall2 _ _ _) and inv it.
      econstructor. rewrite <-H3; etransitivity; eauto; now symmetry.
    - inv Exs; take (Forall2 _ _ _) and inv it.
      econstructor. rewrite <-H3; etransitivity; eauto; now symmetry.
    - inv Exs; take (Forall2 _ _ _) and inv it.
      econstructor; now rewrite <-H2, <-H6.
    - inv Exs; take (Forall2 _ _ _) and inv it.
      econstructor; eauto.
      + apply H2; eauto; reflexivity.
      + now rewrite <-H9.
    - inv Exs; take (Forall2 _ _ _) and inv it.
      econstructor; eauto.
      + apply H2; eauto; reflexivity.
      + apply H4; eauto; reflexivity.
      + now rewrite <-H12.
    - econstructor.
      + eapply Forall2_impl_In; [|apply H2].
        intros * ?? Hs; apply Hs; auto; reflexivity.
      + eapply Forall2_impl_In; [|apply H4].
        intros * ?? Hs; apply Hs; auto; reflexivity.
      + eapply Forall3_EqSt; eauto. solve_proper.
    - econstructor.
      + eapply Forall2_impl_In; [|apply H2].
        intros * ?? Hs; apply Hs; auto; reflexivity.
      + eapply Forall2_impl_In; [|apply H4].
        intros * ?? Hs; apply Hs; auto; reflexivity.
      + eapply Forall3_EqSt; eauto. solve_proper.
    - econstructor; eauto.
      + eapply Forall2_impl_In; [|apply H2].
        intros * ?? Hs; apply Hs; auto; reflexivity.
      + rewrite <-H5; eauto.
      + eapply Forall2_EqSt; eauto. solve_proper.
    - econstructor; eauto.
      + rewrite <-H5; eauto.
      + do 2 (eapply Forall2_impl_In; [|eauto]; intros); simpl in *.
        eapply H12; eauto. reflexivity.
      + eapply Forall2Transpose_EqSt; eauto. solve_proper.
    - econstructor; eauto.
      + eapply H2; eauto. reflexivity.
      + clear H5. do 2 (eapply Forall2_impl_In; [|eauto]; intros; subst).
        eapply H15; eauto. reflexivity.
      + eapply Forall2_impl_In; [|eauto]; intros.
        eapply H13; eauto. reflexivity.
      + eapply Forall2Transpose_EqSt; eauto. solve_proper.
    - econstructor; eauto.
      + eapply Forall2_impl_In; [|apply H2].
        intros * ?? Hs; apply Hs; auto; reflexivity.
      + eapply Forall2_impl_In; [|apply H4].
        intros * ?? Hs; apply Hs; auto; reflexivity.
      + intro k; specialize (H6 k); destruct H6 as (?&Hr).
        apply Hr.
        apply map_st_EqSt_Proper; auto.
        intros ?? ->; reflexivity.
      + eapply clocked_app_morph; eauto.
    - econstructor; eauto.
      eapply Forall2_EqSt; eauto. solve_proper.
  Qed.

  Add Parametric Morphism {prefs} (G : @global prefs) : (sem_equation_ck G)
      with signature Env.Equiv (@EqSt _) ==> @EqSt bool ==> eq ==> Basics.impl
        as sem_equation_ck_morph.
  Proof.
    unfold Basics.impl; intros H H' EH xs xs' Exss eq Hsem.
    inversion_clear Hsem as [????? Hseme Hsemv]. econstructor; eauto.
    - eapply Forall2_impl_In; [|eauto]; intros.
      eapply sem_exp_ck_morph; eauto. reflexivity.
    - eapply Forall2_impl_In; [|eauto]; intros.
      now rewrite <-EH.
  Qed.

  Add Parametric Morphism {prefs} (G : @global prefs) : (sem_block_ck G)
      with signature Env.Equiv (@EqSt _) ==> @EqSt bool ==> eq ==> Basics.impl
        as sem_block_ck_morph.
  Proof.
    unfold Basics.impl. intros H H' EH bs bs' Hbs b Hsem. revert H' bs' EH Hbs.
    eapply sem_block_ck_ind2
      with (P_block := fun H bs b => forall H' bs', Env.Equiv (@EqSt _) H H' -> bs ≡ bs' -> sem_block_ck G H' bs' b)
           (P_exp := fun _ _ _ _ => True)
           (P_equation := fun _ _ _ => True)
           (P_node := fun _ _ _ => True); intros; eauto.
    - constructor. eapply sem_equation_ck_morph; eauto.
    - econstructor; eauto.
      + eapply sem_exp_ck_morph; eauto. reflexivity.
      + intros k. specialize (H4 k) as (Hsem1&Hsem1').
        eapply Forall_Forall in Hsem1; eauto. clear Hsem1'.
        eapply Forall_impl; [|eauto].
        intros ? (?&?). eapply H4; eauto.
        now rewrite <-H5.
        now rewrite <-H6.
  Qed.

  Add Parametric Morphism {prefs} (G : @global prefs) : (sem_node_ck G)
      with signature eq ==> @EqSts svalue ==> @EqSts svalue ==> Basics.impl
        as sem_node_ck_morph.
  Proof.
    unfold Basics.impl; intros f xss xss' Exss yss yss' Eyss Sem.
    induction Sem.
    subst.
    econstructor; try reflexivity; eauto.
    + instantiate (1 := H). now rewrite <-Exss.
    + now rewrite <-Eyss.
    + eapply Forall_forall; intros * Hin.
      eapply Forall_forall in H3; eauto.
      eapply sem_block_ck_morph; eauto. reflexivity.
      now rewrite <-Exss.
    + eapply clocked_node_morph; eauto.
      now rewrite <-Exss.
  Qed.

  (** ** Properties of the [global] environment *)

  Lemma sem_node_ck_cons {prefs} :
    forall (nd : @node prefs) nds enums f xs ys,
      Ordered_nodes (Global enums (nd::nds))
      -> sem_node_ck (Global enums (nd::nds)) f xs ys
      -> nd.(n_name) <> f
      -> sem_node_ck (Global enums nds) f xs ys.
  Proof.
    intros * Hord Hsem Hnf.
    revert Hnf.
    eapply sem_node_ck_ind2
      with
        (P_exp := fun H bk e ss => ~ Is_node_in_exp nd.(n_name) e
                                -> sem_exp_ck (Global enums0 nds) H bk e ss)
        (P_equation := fun H bk eq => ~Is_node_in_eq nd.(n_name) eq
                                   -> sem_equation_ck (Global enums0 nds) H bk eq)
        (P_block := fun H bk d => ~Is_node_in_block nd.(n_name) d
                               -> sem_block_ck (Global enums0 nds) H bk d)
        (P_node := fun f ins outs => nd.(n_name) <> f
                                  -> sem_node_ck (Global enums0 nds) f ins outs). 16:eauto.
      1-16:eauto; intros; try (now econstructor; eauto).
    - econstructor; eauto. apply H1.
      intro. destruct H4. constructor; auto.
    - econstructor; eauto.
      apply H1. intro. destruct H7. constructor. auto.
      apply H3. intro. destruct H7. constructor. auto.
    - econstructor; eauto;
        (eapply Forall2_impl_In; [|eauto]; intros;
         eapply H8; intro; apply H5; constructor);
        [left|right]; apply Exists_exists; eauto.
    - econstructor; eauto;
        (eapply Forall2_impl_In; [|eauto]; intros;
         eapply H8; intro; apply H5; constructor);
        [left|right]; apply Exists_exists; eauto.
    - econstructor; eauto.
      eapply Forall2_impl_In; [|eauto]; intros.
      apply H7; intro contra.
      apply H4; constructor. apply Exists_exists; eauto.
    - econstructor; eauto;
        (eapply Forall2_impl_In; [|eauto]; intros;
         eapply Forall2_impl_In; [|eauto]; intros;
         eapply H10; intro; apply H4;
         constructor;
         do 2 (apply Exists_exists; repeat esplit; eauto)).
    - econstructor; eauto.
      eapply H1.
      2:(clear H4; do 2 (eapply Forall2_impl_In; [|eauto]; intros; subst);
         apply H13).
      3:eapply Forall2_impl_In; [|eauto]; intros; apply H11.
      1-3:(intro; apply H8; constructor; auto; right).
      + left. eapply Exists_exists. exists (Some es0).
        repeat esplit; eauto. eapply Exists_exists; eauto.
      + right. eapply Exists_exists; eauto.
    - inv Hord.
      econstructor; eauto.
      + eapply Forall2_impl_In in H1; [|eauto]; eauto.
        intros * ?? Sem. eapply Sem; intro. take (~ _) and apply it.
        constructor; left. eapply Exists_exists; eauto.
      + eapply Forall2_impl_In in H3; eauto. intros * ?? Hi. simpl. apply Hi. intro.
        take (~ _) and apply it. constructor. right. eapply Exists_exists; eauto.
      + intro k. take (forall k, _ /\ _) and specialize (it k) as (? & Hk).
        apply Hk. intro Hn. subst. take (~ _) and apply it. eapply INEapp2.
    - econstructor; eauto.
      clear H0 H2. induction H1; eauto.
      constructor. apply H0. intro. destruct H3. now constructor.
      apply IHForall2. intro. destruct H3. unfold Is_node_in_eq.
      simpl. rewrite Exists_cons. right. auto.
    - econstructor.
      eapply H1. intro. apply H2. constructor; auto.
    - econstructor; eauto.
      + eapply H1; intro. eapply H4.
        constructor; auto.
      + intros k. specialize (H3 k) as (Hsem'&Hsem'').
        eapply Forall_Forall in Hsem'; eauto. clear Hsem''.
        eapply Forall_impl_In; [|eauto]; intros ? Hin (?&?).
        eapply H3. intro.
        eapply H4. constructor; left.
        eapply Exists_exists; eauto.
    - rewrite find_node_other with (1:=H7) in H0.
      eapply Snode; eauto.
      eapply Forall_impl_In with (2:=H4).
      apply find_node_later_not_Is_node_in with (1:=Hord) in H0.
      intros eq Hin. intro Hini.
      rewrite Is_node_in_Forall in H0.
      apply Forall_forall with (1:=H0) in Hin.
      auto.
  Qed.

  Lemma sem_block_ck_cons {prefs} :
    forall (nd : @node prefs) nds enums bck Hi bk,
      Ordered_nodes (Global enums (nd::nds))
      -> sem_block_ck (Global enums (nd::nds)) Hi bk bck
      -> ~Is_node_in_block nd.(n_name) bck
      -> sem_block_ck (Global enums nds) Hi bk bck.
  Proof.
    intros * Hord Hsem Hnf.
    revert Hnf.
    eapply sem_block_ck_ind2
      with
        (P_exp := fun H bk e ss => ~ Is_node_in_exp nd.(n_name) e
                                -> sem_exp_ck (Global enums0 nds) H bk e ss)
        (P_equation := fun H bk eq => ~Is_node_in_eq nd.(n_name) eq
                                   -> sem_equation_ck (Global enums0 nds) H bk eq)
        (P_block := fun H bk d => ~Is_node_in_block nd.(n_name) d
                               -> sem_block_ck (Global enums0 nds) H bk d)
        (P_node := fun f ins outs => nd.(n_name) <> f
                                  -> sem_node_ck (Global enums0 nds) f ins outs). 16:eauto.
      1-16:eauto; intros; try (now econstructor; eauto).
    - econstructor; eauto. apply H1.
      intro. destruct H4. constructor; auto.
    - econstructor; eauto.
      apply H1. intro. destruct H7. constructor. auto.
      apply H3. intro. destruct H7. constructor. auto.
    - econstructor; eauto;
        (eapply Forall2_impl_In; [|eauto]; intros;
         eapply H8; intro; apply H5; constructor);
        [left|right]; apply Exists_exists; eauto.
    - econstructor; eauto;
        (eapply Forall2_impl_In; [|eauto]; intros;
         eapply H8; intro; apply H5; constructor);
        [left|right]; apply Exists_exists; eauto.
    - econstructor; eauto.
      eapply Forall2_impl_In; [|eauto]; intros.
      apply H7; intro contra.
      apply H4; constructor. apply Exists_exists; eauto.
    - econstructor; eauto;
        (eapply Forall2_impl_In; [|eauto]; intros;
         eapply Forall2_impl_In; [|eauto]; intros;
         eapply H10; intro; apply H4;
         constructor;
         do 2 (apply Exists_exists; repeat esplit; eauto)).
    - econstructor; eauto.
      eapply H1.
      2:(clear H4; do 2 (eapply Forall2_impl_In; [|eauto]; intros; subst);
         apply H13).
      3:eapply Forall2_impl_In; [|eauto]; intros; apply H11.
      1-3:(intro; apply H8; constructor; auto; right).
      + left. eapply Exists_exists. exists (Some es0).
        repeat esplit; eauto. eapply Exists_exists; eauto.
      + right. eapply Exists_exists; eauto.
    - inv Hord.
      econstructor; eauto.
      + eapply Forall2_impl_In in H1; [|eauto]; eauto.
        intros * ?? Sem. eapply Sem; intro. take (~ _) and apply it.
        constructor; left. eapply Exists_exists; eauto.
      + eapply Forall2_impl_In in H3; eauto. intros * ?? Hist. simpl. apply Hist. intro.
        take (~ _) and apply it. constructor. right. eapply Exists_exists; eauto.
      + intro k. take (forall k, _ /\ _) and specialize (it k) as (? & Hk).
        apply Hk. intro Hn. subst. take (~ _) and apply it. eapply INEapp2.
    - econstructor; eauto.
      clear H0 H2. induction H1; eauto.
      constructor. apply H0. intro. destruct H3. now constructor.
      apply IHForall2. intro. destruct H3. unfold Is_node_in_eq.
      simpl. rewrite Exists_cons. right. auto.
    - econstructor.
      eapply H1. intro. apply H2. constructor; auto.
    - econstructor; eauto.
      + eapply H1; intro. eapply H4.
        constructor; auto.
      + intros k. specialize (H3 k) as (Hsem'&Hsem'').
        eapply Forall_Forall in Hsem'; eauto. clear Hsem''.
        eapply Forall_impl_In; [|eauto]; intros ? Hin (?&?).
        eapply H3. intro.
        eapply H4. constructor; left.
        eapply Exists_exists; eauto.
    - rewrite find_node_other with (1:=H7) in H0.
      eapply Snode; eauto.
      eapply Forall_impl_In with (2:=H4).
      apply find_node_later_not_Is_node_in with (1:=Hord) in H0.
      intros eq Hin. intro Hini.
      rewrite Is_node_in_Forall in H0.
      apply Forall_forall with (1:=H0) in Hin.
      auto.
  Qed.

  Corollary sem_blocks_ck_cons {prefs} :
    forall (nd : @node prefs) nds enums b H blocks,
      Ordered_nodes (Global enums (nd :: nds)) ->
      ~ Is_node_in nd.(n_name) blocks ->
      Forall (sem_block_ck (Global enums (nd :: nds)) H b) blocks ->
      Forall (sem_block_ck (Global enums nds) H b) blocks.
  Proof.
    intros * Hord Hnini.
    apply Forall_impl_In.
    intros eq Hin Hsem.
    eapply sem_block_ck_cons; eauto.
    apply Is_node_in_Forall in Hnini.
    apply Forall_forall with (1:=Hnini) (2:=Hin).
  Qed.

  Lemma sem_node_ck_cons' {prefs} :
    forall (nd : @node prefs) nds enums f xs ys,
      Ordered_nodes (Global enums (nd::nds))
      -> sem_node_ck (Global enums nds) f xs ys
      -> nd.(n_name) <> f
      -> sem_node_ck (Global enums (nd::nds)) f xs ys.
  Proof.
    intros * Hord Hsem Hnf.
    revert Hnf.
    eapply sem_node_ck_ind2
      with
        (P_exp := fun H bk e ss => ~ Is_node_in_exp nd.(n_name) e
                                -> sem_exp_ck (Global enums0 (nd::nds)) H bk e ss)
        (P_equation := fun H bk eq => ~Is_node_in_eq nd.(n_name) eq
                                   -> sem_equation_ck (Global enums0 (nd::nds)) H bk eq)
        (P_block := fun H bk d => ~Is_node_in_block nd.(n_name) d
                               -> sem_block_ck (Global enums0 (nd::nds)) H bk d)
        (P_node := fun f ins outs => nd.(n_name) <> f
                                  -> sem_node_ck (Global enums0 (nd::nds)) f ins outs). 16:eauto.
      1-16:eauto; intros; try (now econstructor; eauto).
    - econstructor; eauto. apply H1.
      intro. destruct H4. constructor; auto.
    - econstructor; eauto.
      apply H1. intro. destruct H7. constructor. auto.
      apply H3. intro. destruct H7. constructor. auto.
    - econstructor; eauto;
        (eapply Forall2_impl_In; [|eauto]; intros;
         eapply H8; intro; apply H5; constructor);
        [left|right]; apply Exists_exists; eauto.
    - econstructor; eauto;
        (eapply Forall2_impl_In; [|eauto]; intros;
         eapply H8; intro; apply H5; constructor);
        [left|right]; apply Exists_exists; eauto.
    - econstructor; eauto.
      eapply Forall2_impl_In; [|eauto]; intros.
      apply H7; intro contra.
      apply H4; constructor. apply Exists_exists; eauto.
    - econstructor; eauto;
        (eapply Forall2_impl_In; [|eauto]; intros;
         eapply Forall2_impl_In; [|eauto]; intros;
         eapply H10; intro; apply H4;
         constructor;
         do 2 (apply Exists_exists; repeat esplit; eauto)).
    - econstructor; eauto.
      eapply H1.
      2:(clear H4; do 2 (eapply Forall2_impl_In; [|eauto]; intros; subst);
         apply H13).
      3:eapply Forall2_impl_In; [|eauto]; intros; apply H11.
      1-3:(intro; apply H8; constructor; auto; right).
      + left. eapply Exists_exists. exists (Some es0).
        repeat esplit; eauto. eapply Exists_exists; eauto.
      + right. eapply Exists_exists; eauto.
    - inv Hord.
      econstructor; eauto.
      + eapply Forall2_impl_In in H1; [|eauto]; eauto.
        intros * ?? Sem. eapply Sem; intro. take (~ _) and apply it.
        constructor; left. eapply Exists_exists; eauto.
      + eapply Forall2_impl_In in H3; eauto. intros * ?? Hi. simpl. apply Hi. intro.
        take (~ _) and apply it. constructor. right. eapply Exists_exists; eauto.
      + intro k. take (forall k, _ /\ _) and specialize (it k) as (? & Hk).
        apply Hk. intro Hn. subst. take (~ _) and apply it. eapply INEapp2.
    - econstructor; eauto.
      clear H0 H2. induction H1; eauto.
      constructor. apply H0. intro. destruct H3. now constructor.
      apply IHForall2. intro. destruct H3. unfold Is_node_in_eq.
      simpl. rewrite Exists_cons. right. auto.
    - econstructor.
      eapply H1. intro. apply H2. constructor; auto.
    - econstructor; eauto.
      + eapply H1; intro. eapply H4.
        constructor; auto.
      + intros k. specialize (H3 k) as (Hsem'&Hsem'').
        eapply Forall_Forall in Hsem'; eauto. clear Hsem''.
        eapply Forall_impl_In; [|eauto]; intros ? Hin (?&?).
        eapply H3. intro.
        eapply H4. constructor; left.
        eapply Exists_exists; eauto.
    - assert (~ Is_node_in (n_name nd) (n_blocks n)) as Hnin.
      { apply find_node_later_not_Is_node_in with (1:=Hord) in H0; auto. }
      rewrite <-find_node_other with (1:=H7) in H0.
      eapply Snode; eauto.
      eapply Forall_impl_In with (2:=H4).
      intros eq Hin. intro Hini.
      rewrite Is_node_in_Forall in Hnin.
      apply Forall_forall with (1:=Hnin) in Hin.
      auto.
  Qed.

  Lemma sem_block_ck_cons' {prefs} :
    forall (nd : @node prefs) nds enums bck Hi bk,
      Ordered_nodes (Global enums (nd::nds))
      -> sem_block_ck (Global enums nds) Hi bk bck
      -> ~Is_node_in_block nd.(n_name) bck
      -> sem_block_ck (Global enums (nd::nds)) Hi bk bck.
  Proof.
    intros * Hord Hsem Hnf.
    revert Hnf.
    eapply sem_block_ck_ind2
      with
        (P_exp := fun H bk e ss => ~ Is_node_in_exp nd.(n_name) e
                                -> sem_exp_ck (Global enums0 (nd::nds)) H bk e ss)
        (P_equation := fun H bk eq => ~Is_node_in_eq nd.(n_name) eq
                                   -> sem_equation_ck (Global enums0 (nd::nds)) H bk eq)
        (P_block := fun H bk d => ~Is_node_in_block nd.(n_name) d
                               -> sem_block_ck (Global enums0 (nd::nds)) H bk d)
        (P_node := fun f ins outs => nd.(n_name) <> f
                                  -> sem_node_ck (Global enums0 (nd::nds)) f ins outs). 16:eauto.
      1-16:eauto; intros; try (now econstructor; eauto).
    - econstructor; eauto. apply H1.
      intro. destruct H4. constructor; auto.
    - econstructor; eauto.
      apply H1. intro. destruct H7. constructor. auto.
      apply H3. intro. destruct H7. constructor. auto.
    - econstructor; eauto;
        (eapply Forall2_impl_In; [|eauto]; intros;
         eapply H8; intro; apply H5; constructor);
        [left|right]; apply Exists_exists; eauto.
    - econstructor; eauto;
        (eapply Forall2_impl_In; [|eauto]; intros;
         eapply H8; intro; apply H5; constructor);
        [left|right]; apply Exists_exists; eauto.
    - econstructor; eauto.
      eapply Forall2_impl_In; [|eauto]; intros.
      apply H7; intro contra.
      apply H4; constructor. apply Exists_exists; eauto.
    - econstructor; eauto;
        (eapply Forall2_impl_In; [|eauto]; intros;
         eapply Forall2_impl_In; [|eauto]; intros;
         eapply H10; intro; apply H4;
         constructor;
         do 2 (apply Exists_exists; repeat esplit; eauto)).
    - econstructor; eauto.
      eapply H1.
      2:(clear H4; do 2 (eapply Forall2_impl_In; [|eauto]; intros; subst);
         apply H13).
      3:eapply Forall2_impl_In; [|eauto]; intros; apply H11.
      1-3:(intro; apply H8; constructor; auto; right).
      + left. eapply Exists_exists. exists (Some es0).
        repeat esplit; eauto. eapply Exists_exists; eauto.
      + right. eapply Exists_exists; eauto.
    - inv Hord.
      econstructor; eauto.
      + eapply Forall2_impl_In in H1; [|eauto]; eauto.
        intros * ?? Sem. eapply Sem; intro. take (~ _) and apply it.
        constructor; left. eapply Exists_exists; eauto.
      + eapply Forall2_impl_In in H3; eauto. intros * ?? Hist. simpl. apply Hist. intro.
        take (~ _) and apply it. constructor. right. eapply Exists_exists; eauto.
      + intro k. take (forall k, _ /\ _) and specialize (it k) as (? & Hk).
        apply Hk. intro Hn. subst. take (~ _) and apply it. eapply INEapp2.
    - econstructor; eauto.
      clear H0 H2. induction H1; eauto.
      constructor. apply H0. intro. destruct H3. now constructor.
      apply IHForall2. intro. destruct H3. unfold Is_node_in_eq.
      simpl. rewrite Exists_cons. right. auto.
    - econstructor.
      eapply H1. intro. apply H2. constructor; auto.
    - econstructor; eauto.
      + eapply H1; intro. eapply H4.
        constructor; auto.
      + intros k. specialize (H3 k) as (Hsem'&Hsem'').
        eapply Forall_Forall in Hsem'; eauto. clear Hsem''.
        eapply Forall_impl_In; [|eauto]; intros ? Hin (?&?).
        eapply H3. intro.
        eapply H4. constructor; left.
        eapply Exists_exists; eauto.
    - assert (~ Is_node_in (n_name nd) (n_blocks n)) as Hnin.
      { apply find_node_later_not_Is_node_in with (1:=Hord) in H0; auto. }
      rewrite <-find_node_other with (1:=H7) in H0.
      eapply Snode; eauto.
      eapply Forall_impl_In with (2:=H4).
      intros eq Hin. intro Hini.
      rewrite Is_node_in_Forall in Hnin.
      apply Forall_forall with (1:=Hnin) in Hin.
      auto.
  Qed.

  Corollary sem_blocks_ck_cons' {prefs} :
    forall (nd : @node prefs) nds enums b H blocks,
      Ordered_nodes (Global enums (nd :: nds)) ->
      ~ Is_node_in nd.(n_name) blocks ->
      Forall (sem_block_ck (Global enums nds) H b) blocks ->
      Forall (sem_block_ck (Global enums (nd :: nds)) H b) blocks.
  Proof.
    intros * Hord Hnini.
    apply Forall_impl_In.
    intros eq Hin Hsem.
    eapply sem_block_ck_cons'; eauto.
    apply Is_node_in_Forall in Hnini.
    apply Forall_forall with (1:=Hnini) (2:=Hin).
  Qed.

  Lemma sem_node_ck_cons_iff {prefs} :
    forall (n : @node prefs) nds enums f xs ys,
      Ordered_nodes (Global enums (n::nds)) ->
      n_name n <> f ->
      sem_node_ck (Global enums nds) f xs ys <->
      sem_node_ck (Global enums (n::nds)) f xs ys.
  Proof.
    intros * Hord Hname.
    split; intros Hsem.
    - eapply sem_node_ck_cons'; eauto.
    - eapply sem_node_ck_cons; eauto.
  Qed.

  Lemma sc_when :
    forall H b x ty k ck xs ys rs,
      sem_var H x xs ->
      sem_clock H b ck (abstract_clock ys) ->
      when k ys xs rs ->
      sem_clock H b (Con ck x (ty, k)) (abstract_clock rs).
  Proof.
    cofix Cofix. intros * Hsemv Hsemc Hwhen.
    unfold_Stv rs; inv Hwhen; rewrite unfold_Stream; simpl;
      rewrite unfold_Stream in Hsemc; simpl in Hsemc.
    - econstructor; eauto.
      apply sem_var_step in Hsemv. apply sc_step in Hsemc.
      eapply Cofix; eauto; reflexivity.
    - eapply Son_abs2; eauto.
      apply sem_var_step in Hsemv. apply sc_step in Hsemc.
      eapply Cofix; eauto; reflexivity.
    - econstructor; eauto.
      apply sem_var_step in Hsemv. apply sc_step in Hsemc.
      eapply Cofix; eauto; reflexivity.
  Qed.

  Lemma sc_merge :
    forall H b ck x tx xs vs ss,
      vs <> [] ->
      sem_var H x xs ->
      Forall2 (fun i v => sem_clock H b (Con ck x (tx, i)) (abstract_clock v)) (seq 0 (length vs)) vs ->
      merge xs vs ss ->
      sem_clock H b ck (abstract_clock ss).
  Proof.
    intros * Hlen Hsemv Hsv Hmerge.
    rewrite sem_clock_equiv. apply CIStr.sem_var_impl in Hsemv.
    setoid_rewrite sem_clock_equiv in Hsv.
    rewrite merge_spec in Hmerge.
    intros n. specialize (Hmerge n) as [(Hx&Hvs&Hs)|(?&?&?&?&?&Hx&Heq&_&Hvp&Hva&Hs)].
    - rewrite tr_Stream_ac, Hs.
      specialize (Hsemv n); rewrite tr_Stream_nth, Hx in Hsemv.
      destruct vs; try congruence.
      inv Hsv. specialize (H3 n). inv H3; auto.
      1,2:exfalso; eapply IStr.sem_var_instant_det in Hsemv; eauto; congruence.
    - rewrite tr_Stream_ac, Hs.
      eapply Forall2_EqSt in Hsv; eauto.
      2:{ intros ????? Eq ?; subst. intros n'. now rewrite <-Eq. }
      eapply Forall2_ignore1, Forall_forall with (x:=x2) in Hsv as (?&_&Hck); eauto with datatypes.
      specialize (Hck n). rewrite tr_Stream_ac, Hvp in Hck. inv Hck; auto.
  Qed.

  Hint Resolve Env.find_1 Env.find_2.

  Lemma sc_inst:
    forall H H' b b' ck ck' bck sub cks,
      instck bck sub ck = Some ck' ->
      sem_clock H b ck cks ->
      sem_clock H' b' bck b ->
      (forall x x',
          Is_free_in_clock x ck ->
          sub x = Some x' ->
          orel (@EqSt svalue) (Env.find x H) (Env.find x' H')) ->
      sem_clock H' b' ck' cks.
  Proof.
    intros * Hinst Hck Hbck Henv.
    rewrite sem_clock_equiv in *.
    intros n. specialize (Hck n). specialize (Hbck n).
    assert (forall x x' n, Is_free_in_clock x ck -> sub x = Some x' -> orel (eq (A:=svalue)) (Env.find x (CIStr.tr_history H n)) (Env.find x' (CIStr.tr_history H' n))) as Henv'.
    { intros * Hfree Hsub. specialize (Henv x x' Hfree Hsub).
    eapply tr_history_find_orel in Henv; eauto. } clear Henv.
    unfold tr_Stream in *.
    revert H H' b b' ck' bck cks sub Hinst Hck Hbck Henv'.
    induction ck; intros.
    - inv Hinst. inv Hck; auto.
    - inversion Hinst as [Hcase]. cases_eqn Hcase. inv Hcase.
      inv Hck.
      1,2:econstructor;eauto. 5:eapply IStr.Son_abs2; eauto.
      2,4,6:(unfold IStr.sem_var_instant in *;
             specialize (Henv' i i0 n (FreeCon1 _ _ _) Hcase1); rewrite H5 in Henv';
             inv Henv'; auto).
      * rewrite H4 in *; eapply IHck in Hcase0; eauto.
      * rewrite H4 in *; eapply IHck in Hcase0; eauto.
      * eapply IHck with (cks:=Streams.const true) in Hcase0; eauto.
        rewrite const_nth in Hcase0; auto. rewrite const_nth; eauto.
  Qed.

  Lemma sc_inst':
      forall H' H b b' ck ck' bck sub cks,
      instck bck sub ck = Some ck' ->
      sem_clock H' b' ck' cks ->
      sem_clock H' b' bck b ->
      (forall x x',
          Is_free_in_clock x ck ->
          sub x = Some x' ->
          orel (@EqSt svalue) (Env.find x H) (Env.find x' H')) ->
      sem_clock H b ck cks.
  Proof.
    intros * Hinst Hck Hbck Henv.
    rewrite sem_clock_equiv in *.
    intros n. specialize (Hck n). specialize (Hbck n).
    assert (forall x x' n, Is_free_in_clock x ck -> sub x = Some x' -> orel (eq (A:=svalue)) (Env.find x (CIStr.tr_history H n)) (Env.find x' (CIStr.tr_history H' n))) as Henv'.
    { intros * Hfree Hsub. specialize (Henv x x' Hfree Hsub).
    eapply tr_history_find_orel in Henv; eauto. } clear Henv.
    unfold tr_Stream in *.
    revert H H' b b' ck' bck cks sub Hinst Hck Hbck Henv'.
    induction ck; intros; simpl in *.
    - inv Hinst. eapply IStr.sem_clock_instant_det in Hck; eauto. rewrite Hck; auto.
    - inversion Hinst as [Hcase]. cases_eqn Hcase. inv Hcase.
      inv Hck.
      1,2:econstructor;eauto. 5:eapply IStr.Son_abs2; eauto.
      2,4,6:(unfold IStr.sem_var_instant in *;
             specialize (Henv' i i0 n (FreeCon1 _ _ _) Hcase1); rewrite H5 in Henv';
             inv Henv'; auto).
      * rewrite H4 in *; eapply IHck in Hcase0; eauto.
      * rewrite H4 in *; eapply IHck in Hcase0; eauto.
      * eapply IHck with (cks:=Streams.const true) in Hcase0; eauto.
        rewrite const_nth in Hcase0; auto. rewrite const_nth; eauto.
  Qed.

  Lemma sc_parent :
    forall H b ck lck ss,
      Forall2 (sem_clock H b) lck (map abstract_clock ss) ->
      In ck lck ->
      Forall (fun ck' => ck' = ck \/ clock_parent ck ck') lck ->
      sem_clock H b ck (clocks_of ss).
  Proof.
    intros * Hsc Hin Hparent.
    pose proof (Forall2_in_left _ _ _ _ Hsc Hin) as [s (Hins & Hsc0)].
    rewrite Forall2_map_2 in Hsc. apply in_map_iff in Hins as [?(?&?)]. subst.
    assert (
        Forall (fun s' => sub_clock (abstract_clock x) (abstract_clock s')) ss
      ) as Hf. {
      apply Forall_forall; intros * Hx0.
      pose proof (Forall2_in_right _ _ _ _ Hsc Hx0) as [? (Hx1&Hsc1)].
      eapply Forall_forall in Hx1; eauto. destruct Hx1.
      subst.
      apply sem_clock_det with (2 := Hsc1) in Hsc0. now rewrite Hsc0.
      eapply sub_clock_parent; eauto.
    }
    apply sub_clock_sclocksof in Hf; auto. now rewrite Hf.
  Qed.

  Lemma wc_env_free_in_clock :
    forall x i ck vars,
      wc_env vars ->
      In (x, ck) vars ->
      Is_free_in_clock i ck ->
      exists ick, In (i, ick) vars.
  Proof.
    intros * WC Ix Hfree.
    revert x Ix. induction ck; inv Hfree;
    intros; eapply Forall_forall in WC; eauto; inv WC; eauto.
  Qed.

  Lemma idck_idents :
    forall l, idents l = map fst (idck l).
  Proof.
    unfold idents, idck. induction l; simpl; auto.
    f_equal. auto.
  Qed.

  Ltac simpl_Foralls :=
    repeat
      match goal with
      | H: Forall _ [] |- _ => inv H
      | H: Forall _ [_] |- _ => inv H
      | H: Forall _ (_ :: _) |- _ => inv H
      | H: Forall2 _ [_] _ |- _ => inv H
      | H: Forall2 _ [] _ |- _ => inv H
      | H: Forall2 _ _ [_] |- _ => inv H
      | H: Forall2 _ _ [] |- _ => inv H
      end.

  Fact NoDupMembers_idck : forall (xs : list (ident * (type * clock))),
      NoDupMembers (idck xs) <-> NoDupMembers xs.
  Proof.
    intros. repeat rewrite fst_NoDupMembers.
    rewrite <- idck_idents. reflexivity.
  Qed.

  Fact sc_has_base {prefs} : forall H b bck sub (n : @node prefs) ncks ss,
      wc_env (idck (n_in n)) ->
      Forall2 (fun nck => sem_clock H b (stripname nck)) ncks (map abstract_clock ss) ->
      Forall2 (WellInstantiated bck sub) (idck (n_in n)) ncks ->
      sem_clock H b bck (clocks_of ss).
  Proof.
    intros * WCin Hscin WIi.
    pose proof (wc_env_has_Cbase _ WCin) as [i Hin].
    { rewrite length_idck. exact (n_ingt0 n). }
    apply WellInstantiated_parent in WIi as Hp.
    change (Forall (fun ck => (fun x => x = bck \/ clock_parent bck x) (fst ck))
                   ncks) in Hp.
    rewrite <- Forall_map in Hp.
    eapply sc_parent; eauto.
    now rewrite Forall2_map_1.
    pose proof (Forall2_in_left _ _ _ _ WIi Hin) as [?(?&?& H14)].
    simpl in H14. inv H14. now apply in_map.
  Qed.

  Lemma sc_inst_mask:
    forall H' b b' ck ck' bck sub cks rs,
      instck bck sub ck = Some ck' ->
      sem_clock H' b' bck b ->
      (forall k, exists H, sem_clock H (maskb k rs b) ck (maskb k rs cks) /\
                 (forall x x',
                     Is_free_in_clock x ck ->
                     sub x = Some x' ->
                     orel (fun v1 v2 => EqSt v1 (maskv k rs v2)) (Env.find x H) (Env.find x' H'))) ->
      sem_clock H' b' ck' cks.
  Proof.
    intros * Hinst Hbck Hk.
    rewrite sem_clock_equiv in *. unfold tr_Stream in *.
    intros n. specialize (Hbck n); simpl in Hbck.
    specialize (Hk ((count rs) # n)) as [H [Hck Henv]].
    rewrite sem_clock_equiv in Hck. unfold tr_Stream in Hck.
    specialize (Hck n); simpl in Hck.
    repeat rewrite maskb_nth in Hck.
    repeat rewrite Nat.eqb_refl in Hck.
    assert (forall x x', Is_free_in_clock x ck -> sub x = Some x' -> orel (@eq svalue) (Env.find x (CIStr.tr_history H n)) (Env.find x' (CIStr.tr_history H' n))) as Henv'.
    { intros * Hfree Hsub. specialize (Henv x x' Hfree Hsub).
      eapply tr_history_find_orel_unmask with (n:=n) in Henv.
      assert (relation_equivalence eq (fun v1 v2 => v1 = (if (count rs) # n =? (count rs) # n then v2 else absent))) as Heq.
      { intros x1 x2.
        rewrite Nat.eqb_refl.
        constructor; auto. }
      rewrite Heq; auto.
    } clear Henv.
    revert H H' b b' ck' bck cks sub Hinst Hck Hbck Henv'.
    induction ck; intros.
    - inv Hinst. inv Hck; auto.
    - inversion Hinst as [Hcase]. cases_eqn Hcase. inv Hcase.
      inv Hck.
      1,2:econstructor;eauto. 5:eapply IStr.Son_abs2; eauto.
      2,4,6:(unfold IStr.sem_var_instant in *;
             specialize (Henv' i i0 (FreeCon1 _ _ _) Hcase1); rewrite H5 in Henv';
             inv Henv'; auto).
      * rewrite H4 in *; eapply IHck in Hcase0; eauto.
      * rewrite H4 in *; eapply IHck in Hcase0; eauto.
      * eapply IHck with (cks:=Streams.const true) in Hcase0; eauto.
        rewrite const_nth in Hcase0; auto. rewrite const_nth; eauto.
  Qed.

  Lemma sc_inst_unmask:
    forall H H' b b' ck ck' bck sub cks k rs,
      instck bck sub ck = Some ck' ->
      sem_clock H' b' ck' cks ->
      sem_clock H' b' bck b ->
      (forall x x',
          Is_free_in_clock x ck ->
          sub x = Some x' ->
          orel (fun v1 v2 => EqSt v1 (maskv k rs v2)) (Env.find x H) (Env.find x' H')) ->
      sem_clock H (maskb k rs b) ck (maskb k rs cks).
  Proof.
    intros * Hinst Hck Hbck Henv.
    rewrite sem_clock_equiv in *.
    intros n. specialize (Hck n). specialize (Hbck n).
    assert (forall x x' n, Is_free_in_clock x ck -> sub x = Some x' -> orel (fun v1 v2 => v1 = (if (CStr.count rs) # n =? k then v2 else absent)) (Env.find x (CIStr.tr_history H n)) (Env.find x' (CIStr.tr_history H' n))) as Henv'.
    { intros * Hfree Hsub. specialize (Henv x x' Hfree Hsub).
      eapply tr_history_find_orel_unmask in Henv; eauto. } clear Henv.
    unfold tr_Stream in *.
    revert H H' b b' ck' bck cks sub Hinst Hck Hbck Henv'.
    induction ck; intros; simpl in *.
    - inv Hinst.
      repeat rewrite maskb_nth in *. destruct (_ =? k); auto.
      eapply IStr.sem_clock_instant_det in Hck; eauto.
      rewrite Hck; auto.
    - inversion Hinst as [Hcase]. cases_eqn Hcase. inv Hcase.
      repeat rewrite maskb_nth in *; destruct (_ =? k) eqn:Hcount.
      + inv Hck.
        1,2:econstructor;eauto. 5:eapply IStr.Son_abs2; eauto.
        2,4,6:(unfold IStr.sem_var_instant in *;
               specialize (Henv' i i0 n (FreeCon1 _ _ _) Hcase1); rewrite H5 in Henv';
               inv Henv'; auto; rewrite Hcount; auto).
        * rewrite H4 in *; eapply IHck with (b':=b') in Hcase0; eauto.
          repeat rewrite maskb_nth, Hcount, <- H4 in Hcase0. rewrite <- H4; eauto.
        * rewrite H4 in *; eapply IHck with (b':=b') in Hcase0; eauto.
          repeat rewrite maskb_nth, Hcount in Hcase0; eauto.
        * assert (Htrue:=H4). apply IStr.sem_clock_instant_true_inv in H4; eauto.
          eapply IHck with (b:=b) (b':=b') (cks:=Streams.const true) in Hcase0; eauto.
          repeat rewrite maskb_nth, Hcount in Hcase0. rewrite const_nth in Hcase0; eauto.
          rewrite const_nth; eauto.
      + inv Hck.
        1,2,3:econstructor; eauto.
        2,4,6:(unfold IStr.sem_var_instant in *;
               specialize (Henv' _ _ n (FreeCon1 _ _ _) Hcase1); rewrite H5 in Henv';
               inv Henv'; auto; rewrite Hcount; auto).
        1,3:eapply IHck with (b':=b') (b:=b) (cks:=Streams.const true) in Hcase0; eauto.
        1-5:repeat rewrite maskb_nth, Hcount in *; repeat rewrite const_nth in *; auto.
        eapply IHck in Hcase0; eauto. 2:rewrite <-H4; eauto.
        repeat rewrite maskb_nth, Hcount in Hcase0; eauto.
  Qed.

  Lemma inst_in_eqst_mask:
    forall H Hi xs ys vs i ck bck sub k rs,
      In (i, ck) xs ->
      Forall2 (WellInstantiated bck sub) xs ys ->
      Forall2 (sem_var Hi) (map fst xs) (map (maskv k rs) vs) ->
      Forall2 (fun '(_, o) s => LiftO True (fun x => sem_var H x s) o) ys vs ->
      forall i',
        sub i = Some i' ->
        orel (fun v1 v2 => v1 ≡ maskv k rs v2) (Env.find i Hi) (Env.find i' H).
  Proof.
    intros * Hin WI Hsvi Hsvo i Sub.
    rewrite Forall2_map_1, Forall2_map_2 in Hsvi.
    rewrite Forall2_swap_args in Hsvo.
    eapply Forall2_trans_ex with (1:=Hsvi) in Hsvo. clear Hsvi.
    eapply Forall2_Forall2 in WI; eauto. clear Hsvo.
    eapply Forall2_forall2 in WI as [? WI].
    eapply In_nth in Hin as [n' [Hlen Hin]].
    destruct (nth n' ys (Cbase, None)) eqn:Hy.
    specialize (WI (xH, Cbase) (Cbase, None) _ _ _ Hlen Hin Hy) as ((?&?&?&?)&Hinst).
    simpl in H2; inv H2. apply Env.find_1 in H5; rewrite H5.
    inv Hinst; simpl in *. rewrite Sub in H2; inv H2.
    simpl in H3; inv H3. apply Env.find_2 in H7; rewrite H7.
    constructor. symmetry. rewrite <- H8; eauto.
  Qed.

  (* When function call parameters are well instantiated and have
     the [sem_clock] property, we obtain the same property inside
     the node (Hi = "H inside").
   *)
  Corollary sc_inside_mask {prefs2} :
    forall H Hi b es ss0 bck sub (n : @node prefs2) k rs,
      Forall2 (fun '(_, o) (s : Stream svalue) => LiftO True (fun x1 : ident => sem_var H x1 s) o) (nclocksof es) (concat ss0) ->
      wc_env (idck (n_in n)) ->
      Forall2 (sem_clock H b) (clocksof es) (map abstract_clock (concat ss0)) ->
      Forall2 (WellInstantiated bck sub) (idck (n_in n)) (nclocksof es) ->
      Forall2 (sem_var Hi) (idents (n_in n)) (map (maskv k rs) (concat ss0)) ->
      Forall2 (fun xc => sem_clock Hi (clocks_of (map (maskv k rs) (concat ss0))) (snd xc))
              (idck (n_in n)) (map abstract_clock (map (maskv k rs) (concat ss0))).
  Proof.
    intros * Hse WCin Hscin WIi Hsv.

    rewrite Forall2_map_2 in Hscin. rewrite Forall2_map_2 in Hsv. repeat rewrite Forall2_map_2.
    rewrite clocksof_nclocksof, Forall2_map_1 in Hscin.
    apply Forall2_trans_ex with (1 := WIi) in Hscin as H1.
    eapply Forall2_impl_In; eauto.
    intros (x & ck) xs  Hxin ? ((yck & ny) & Hyin & (Hsub & Hinst) & Hsc).
    simpl in *.
    rewrite ac_mask, clocks_of_mask.
    eapply sc_inst_unmask; eauto.
    - eapply sc_has_base; eauto.
      rewrite Forall2_map_2; auto.
    - clear - Hxin WCin WIi Hse Hsv.
      intros i i' Free Sub.
      pose proof (wc_env_free_in_clock _ _ _ _ WCin Hxin Free) as [].
      eapply inst_in_eqst_mask; eauto.
      rewrite <- idck_idents, Forall2_map_2; eauto.
  Qed.

  Definition def_stream b := enum b 0.

  Lemma sc_outside_mask {prefs1 prefs2} :
    forall (G : @global prefs1) H es b env ncks ss0 ss bck sub (n : @node prefs2) rs,
      Forall (wc_exp G env) es ->
      Forall2 (fun '(_, o1) s => LiftO True (fun x0 : ident => sem_var H x0 s) o1) (nclocksof es) (concat ss0) ->
      Forall2 (fun '(_, o) s => LiftO True (fun x0 => sem_var H x0 s) o) ncks ss ->
      wc_env (idck (n_in n)) ->
      wc_env (idck (n_in n ++ n_out n)) ->
      Forall2 (sem_clock H b) (clocksof es) (map abstract_clock (concat ss0)) ->
      Forall2 (WellInstantiated bck sub) (idck (n_in n)) (nclocksof es) ->
      Forall2 (WellInstantiated bck sub) (idck (n_out n)) ncks ->
      (forall k, exists Hi,
            Forall2 (fun xc => sem_clock Hi (clocks_of (map (maskv k rs) (concat ss0))) (snd xc))
                    (idck (n_out n)) (map abstract_clock (map (maskv k rs) ss)) /\
            Forall2 (sem_var Hi) (idents (n_in n)) (map (maskv k rs) (concat ss0)) /\
            Forall2 (sem_var Hi) (idents (n_out n)) (map (maskv k rs) ss)) ->
      Forall2 (sem_clock H b) (map fst ncks) (map abstract_clock ss).
  Proof.
    intros * Hwc Hsvar Hse2 WCin WCinout Hscin WIi WIo Hk.

    rewrite clocksof_nclocksof, Forall2_map_1, Forall2_map_2 in Hscin.
    rewrite Forall2_map_1, Forall2_map_2.
    assert (length ncks = length (idck (n_out n))) as Hlen1.
    { apply Forall2_length in WIo; auto. }
    assert (length ncks = length ss) as Hlen2.
    { specialize (Hk 0) as (?&_&_&Hf).
      rewrite Forall2_map_2, idck_idents, Forall2_map_1 in Hf.
      apply Forall2_length in Hf.
      setoid_rewrite Hlen1; auto. }
    eapply Forall2_forall2; split; eauto.
    intros [? ?] ? ? [? ?] ? Hlen Hnth1 Hnth2; simpl; subst.
    eapply sc_inst_mask; eauto.
    - eapply Forall2_forall2 in WIo as [? WIo].
      rewrite Hlen1 in Hlen.
      specialize (WIo (xH, Cbase) _ _ _ _ Hlen eq_refl Hnth1).
      inv WIo; eauto.
    - eapply sc_has_base; eauto. rewrite Forall2_map_2; eauto.
    - intros k.
      specialize (Hk k) as (Hi&?&?&?).
      exists Hi. split.
      + eapply Forall2_forall2 in H0 as [? Hck].
        rewrite Hlen1 in Hlen.
        specialize (Hck (xH, Cbase) (abstract_clock (def_stream b)) _ _ _ Hlen eq_refl eq_refl).
        erewrite clocks_of_mask, map_map, map_nth', ac_mask in Hck; eauto.
        rewrite <- Hlen2, Hlen1; auto.
      + intros i i' Free Sub.
        destruct (nth n0 (idck (n_out n)) (1%positive, Cbase)) as (yck, ny) eqn:Hy.
        assert (In (yck, ny) (idck (n_in n ++ n_out n))) as Hyin2.
        { rewrite idck_app. apply in_or_app. right.
          rewrite <- Hy. apply nth_In. congruence. }
        pose proof (wc_env_free_in_clock _ _ _ _ WCinout Hyin2 Free) as [].
        eapply inst_in_eqst_mask with (vs:=(concat ss0++ss)). 1,5:eauto.
        * rewrite idck_app. eapply Forall2_app; eauto.
        * rewrite idck_app, map_app, map_app. repeat rewrite <- idck_idents.
          eapply Forall2_app; eauto.
        * eapply Forall2_app; eauto.
  Qed.

  Definition sem_clock_inputs {prefs} (G : @global prefs) (f : ident) (xs : list (Stream svalue)): Prop :=
    exists H n,
      find_node f G = Some n /\
      Forall2 (sem_var H) (idents (n_in n)) xs /\
      Forall2 (fun xc => sem_clock H (clocks_of xs) (snd xc))
              (idck (n_in n)) (map abstract_clock xs).

  Lemma sem_clock_inputs_cons {prefs} :
    forall enums (nodes : list (@node prefs)) f n ins,
      n_name n <> f ->
      sem_clock_inputs (Global enums nodes) f ins <-> sem_clock_inputs (Global enums (n :: nodes)) f ins.
  Proof.
    intros * Hname.
    split; intros (H & n' & Hfind &?&?);
      exists H, n'; repeat split; auto.
    - rewrite find_node_other; eauto.
    - erewrite <- find_node_other; eauto.
  Qed.

  Lemma inputs_clocked_vars {prefs} :
    forall enums (nodes : list (@node prefs)) n H f ins,
      sem_clock_inputs (Global enums (n :: nodes)) f ins ->
      n_name n = f ->
      wc_env (idck (n_in n)) ->
      Forall2 (sem_var H) (idents (n_in n)) ins ->
      Forall2 (fun xc => sem_clock H (clocks_of ins) (snd xc)) (idck (n_in n)) (map abstract_clock ins).
  Proof.
    intros * (H'&n'& Hfind & Hv & Hscin) Hnf Wcin Hins; subst.
    rewrite find_node_now in Hfind; auto. inv Hfind.
    pose proof (sem_var_env_eq _ _ _ _ Hins Hv) as Horel.
    rewrite idck_idents in *. rewrite Forall2_map_1 in Hv, Hins.
    eapply Forall2_impl_In; [|eauto]. intros; simpl in *.
    eapply sem_clock_same_find; eauto.
    unfold wc_env in Wcin. eapply Forall_forall in H0; [|eauto]. auto.
  Qed.

  Lemma sem_clocks_det : forall H H' b ins outs vins vouts ss,
      wc_env (idck (ins ++ outs)) ->
      Forall2 (sem_var H) (idents ins) vins ->
      Forall2 (sem_var H) (idents outs) vouts ->
      Forall2 (sem_var H') (idents ins) vins ->
      Forall2 (sem_var H') (idents outs) vouts ->
      Forall2 (fun xc => sem_clock H b (snd xc)) (idck outs) ss ->
      Forall2 (fun xs => sem_clock H' b (snd xs)) (idck outs) ss.
  Proof.
    intros * Hwc Hi1 Ho1 Hi2 Ho2 Hck.
    eapply Forall2_impl_In; [|eauto]. intros [? ?] ? Hin1 Hin2 Hsc.
    rewrite idck_app in Hwc. assert (Hwc':=Hwc). apply Forall_app_weaken in Hwc.
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
                   (idck ins ++ idck outs)) as Hvars.
    { unfold idck. rewrite <- map_app, Forall_map.
      eapply Forall2_Forall2 in Ho; [|eapply Ho']. clear Ho'.
      eapply Forall2_ignore2 in Ho.
      eapply Forall_impl; [|eauto]. intros (?&?&?) (?&?&?&?).
      intros ? Hvar. eapply IStr.sem_var_instant_det in H2; eauto; subst. assumption.
    } clear Ho Ho'.

    revert b b0 Hsc.
    induction Hin1; intros; inv Hsc; [eapply IStr.Sbase|eapply IStr.Son|eapply IStr.Son_abs1|eapply IStr.Son_abs2]; eauto.
    - rewrite H5. eapply IHHin1. congruence.
    - eapply Forall_forall in Hvars; eauto; simpl in *; eauto.
    - rewrite H5. eapply IHHin1. congruence.
    - eapply Forall_forall in Hvars; eauto; simpl in *; eauto.
    - specialize (IHHin1 b0 (Streams.const true)). rewrite tr_Stream_const in IHHin1; eauto.
    - eapply Forall_forall in Hvars; eauto; simpl in *; eauto.
  Qed.

  (** First step of the proof:
      Prove that every named stream of the node is aligned with the clock
      of its variable *)
  Section sc_inv.
    Context {prefs : PS.t}.
    Variable (G : @global prefs).

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
                (idck (n_in n)) (map abstract_clock xs) ->
        Forall2 (fun xc => sem_clock H (clocks_of xs) (snd xc))
                (idck (n_out n)) (map abstract_clock os).
    Proof.
      intros * Hwc Hsem Hfind Hins Houts Hckins.
      eapply Hnode in Hsem. 2:(repeat esplit; eauto).
      destruct Hwc as (_&Hwc&_). inv Hsem.
      rewrite Hfind in H1. inv H1.
      eapply sem_clocks_det; eauto.
      rewrite Forall2_map_2.
      unfold idck, idents in *.
      rewrite Forall2_map_1 in H3. rewrite Forall2_map_1.
      eapply Forall2_impl_In; [|eauto]; intros (?&?&?) ? Hin1 Hin2 Hvar; simpl in *.
      destruct H6 as (_&Hinv).
      eapply Forall_map, Forall_forall in Hinv as (?&Hvar'&Hck'); eauto using in_or_app.
      eapply sem_var_det in Hvar; eauto.
      rewrite <-Hvar; auto.
    Qed.

    Definition sc_var_inv' env (H : history) (b : Stream bool) : ident -> Prop :=
      fun x => forall ck xs,
          In (x, ck) env ->
          sem_var H x xs ->
          sem_clock H b ck (abstract_clock xs).

    Lemma sc_var_inv_sc_var_inv' : forall env H b,
        NoDupMembers env ->
        sc_var_inv env H b ->
        Forall (sc_var_inv' env H b) (map fst env).
    Proof.
      intros * Hndup Hinv'.
      unfold sc_var_inv' in Hinv'.
      rewrite Forall_map.
      eapply Forall_impl_In; [|eauto].
      intros (?&?) Hin (?&Hvar&Hck) ?? Hin' Hvar'.
      eapply NoDupMembers_det in Hin; eauto; subst.
      eapply sem_var_det in Hvar; eauto. rewrite Hvar. assumption.
    Qed.

    Lemma sc_var_inv'_sc_var_inv : forall env H b,
        Forall (fun x => exists v, sem_var H x v) (map fst env) ->
        Forall (sc_var_inv' env H b) (map fst env) ->
        sc_var_inv env H b.
    Proof.
      intros * Hvars Hinv.
      unfold sc_var_inv'.
      rewrite Forall_map in Hinv, Hvars.
      eapply Forall_Forall in Hinv; [|eapply Hvars]. clear Hvars.
      eapply Forall_impl_In; [|eauto].
      intros (?&?) Hin ((v&Hvar)&Hsc).
      exists v. split; eauto.
    Qed.

    Definition sc_exp_inv env (H : history) (b : Stream bool) : exp -> nat -> Prop :=
      fun e k => forall ss,
          wc_exp G env e ->
          Sem.sem_exp G H b e ss ->
          anon_sem_exp G H b e ->
          sem_clock H b (nth k (clockof e) Cbase) (abstract_clock (nth k ss (def_stream b))).

    Fact P_exps_sc_exp_inv : forall env H b es ss k,
        Forall (wc_exp G env) es ->
        Forall2 (Sem.sem_exp G H b) es ss ->
        Forall (anon_sem_exp G H b) es ->
        LCA.P_exps (sc_exp_inv env H b) es k ->
        sem_clock H b (nth k (clocksof es) Cbase) (abstract_clock (nth k (concat ss) (def_stream b))).
    Proof.
      induction es; intros * Hwc Hsem Hanon Hp;
        inv Hwc; inv Hsem; inv Hanon; simpl. inv Hp.
      assert (length y = numstreams a) as Hlen by (eapply sem_exp_numstreams; eauto).
      inv Hp.
      - (* now *)
        rewrite app_nth1. 2:rewrite length_clockof_numstreams; auto.
        rewrite app_nth1. 2:congruence.
        eapply H10; eauto.
      - (* later *)
        rewrite app_nth2. 1,2:rewrite length_clockof_numstreams; auto.
        rewrite app_nth2. 1,2:rewrite Hlen; auto.
    Qed.

    Fact P_exps_sc_exp_inv_all : forall env H b es ss,
        Forall (wc_exp G env) es ->
        Forall2 (Sem.sem_exp G H b) es ss ->
        Forall (anon_sem_exp G H b) es ->
        (forall k, k < length (annots es) -> LCA.P_exps (sc_exp_inv env H b) es k) ->
        Forall2 (sem_clock H b) (clocksof es) (map abstract_clock (concat ss)).
    Proof.
      intros * Hwc Hsem Hanon Hk.
      assert (length (clocksof es) = length (concat ss)) as Hlen.
      { rewrite length_clocksof_annots. symmetry.
        eapply sem_exps_numstreams; eauto. }
      eapply Forall2_forall2; split. rewrite map_length; auto.
      intros * Hn ? ?; subst.
      erewrite map_nth' with (d':=def_stream b). 2:congruence.
      erewrite nth_indep with (d':=Cbase); auto.
      eapply P_exps_sc_exp_inv; eauto.
      eapply Hk. rewrite <- length_clocksof_annots; auto.
    Qed.

    Lemma sc_exp_const : forall env H b c,
        sc_exp_inv env H b (Econst c) 0.
    Proof.
      intros * ? Hwc Hsem _; inv Hsem.
      simpl. rewrite H4, ac_const.
      constructor. reflexivity.
    Qed.

    Lemma sc_exp_enum : forall env H b k ty,
        sc_exp_inv env H b (Eenum k ty) 0.
    Proof.
      intros * ? Hwc Hsem _; inv Hsem.
      simpl. rewrite H6, ac_enum.
      constructor. reflexivity.
    Qed.

    Lemma sc_exp_var : forall env H b x ann,
        sc_var_inv' env H b x ->
        sc_exp_inv env H b (Evar x ann) 0.
    Proof.
      intros *  Hvar ss Hwc Hsem _; inv Hsem; simpl.
      eapply Hvar; eauto. inv Hwc; auto.
    Qed.

    Lemma sc_exp_unop : forall env H b op e1 ann,
        sc_exp_inv env H b e1 0 ->
        sc_exp_inv env H b (Eunop op e1 ann) 0.
    Proof.
      intros * He1 ss Hwc Hsem Hanon; inv Hwc; inv Hsem; inv Hanon; simpl.
      eapply He1 in H8; eauto. rewrite H4 in H8; simpl in H8.
      rewrite <- ac_lift1; eauto.
    Qed.

    Lemma sc_exp_binop : forall env H b op e1 e2 ann,
        sc_exp_inv env H b e1 0 ->
        sc_exp_inv env H b e2 0 ->
        sc_exp_inv env H b (Ebinop op e1 e2 ann) 0.
    Proof.
      intros * He1 He2 ss Hwc Hsem Hanon; inv Hwc; inv Hsem; inv Hanon; simpl.
      eapply He1 in H9; eauto. rewrite H6 in H9; simpl in H9.
      rewrite <- ac_lift2; eauto.
    Qed.

    Lemma sc_exp_fby : forall env H b e0s es ann k,
        k < length ann ->
        LCA.P_exps (sc_exp_inv env H b) e0s k ->
        sc_exp_inv env H b (Efby e0s es ann) k.
    Proof.
      intros * Hk Hexps ss Hwc Hsem Hanon; simpl.
      inv Hwc. inv Hsem. inv Hanon.
      eapply P_exps_sc_exp_inv in Hexps; eauto.
      rewrite Forall2_eq in H5. rewrite H5.
      assert (Forall2 (fun x y => abstract_clock x ≡ abstract_clock y) (concat s0ss) ss).
      { clear - H14. eapply Forall3_ignore2 in H14.
        eapply Forall2_impl_In; eauto.
        intros ? ? _ _ [? ?]. apply ac_fby1 in H; auto. }
      apply Forall2_forall2 in H0 as [_ Hac].
      erewrite <- Hac; eauto.
      erewrite sem_exps_numstreams, <- length_clocksof_annots, <- H5, map_length; eauto.
    Qed.

    Lemma sc_exp_arrow : forall env H b e0s es ann k,
        k < length ann ->
        LCA.P_exps (sc_exp_inv env H b) e0s k ->
        LCA.P_exps (sc_exp_inv env H b) es k ->
        sc_exp_inv env H b (Earrow e0s es ann) k.
    Proof.
      intros * Hk He0s Hes ss Hwc Hsem Hanon; simpl.
      inv Hwc. inv Hsem. inv Hanon.
      eapply P_exps_sc_exp_inv in He0s; eauto.
      rewrite Forall2_eq in H5. rewrite H5.
      assert (Forall2 (fun x y => abstract_clock x ≡ abstract_clock y) (concat s0ss) ss).
      { clear - H14. eapply Forall3_ignore2 in H14.
        eapply Forall2_impl_In; eauto.
        intros ? ? _ _ [? ?]. apply ac_arrow1 in H; auto. }
      apply Forall2_forall2 in H0 as [_ Hac].
      erewrite <- Hac; eauto.
      erewrite sem_exps_numstreams, <- length_clocksof_annots, <- H5, map_length; eauto.
    Qed.

    Lemma sc_exp_when : forall env H b es x b' ann k,
        k < length (fst ann) ->
        LCA.P_exps (sc_exp_inv env H b) es k ->
        sc_var_inv' env H b x ->
        sc_exp_inv env H b (Ewhen es x b' ann) k.
    Proof.
      intros * Hk Hes Hvar ss Hwc Hsem Hanon; simpl.
      inv Hwc. inv Hsem. inv Hanon.
      eapply P_exps_sc_exp_inv in Hes; eauto.
      assert (Hv:=H13). eapply Hvar in Hv; eauto.
      erewrite map_nth' with (d':=OpAux.bool_velus_type); eauto.
      unfold clock_of_nclock, stripname; simpl.
      eapply Forall_forall in H6. 2:eapply nth_In; rewrite <- H7; eauto.
      eapply sc_when in Hes; eauto. erewrite H6; eauto.
      eapply Forall2_forall2 in H14 as [_ Hwhen].
      eapply Hwhen; eauto.
      replace (length (concat ss0)) with (length (annots es)). rewrite <- length_clocksof_annots, <- H7; eauto.
      symmetry. eapply sem_exps_numstreams; eauto.
    Qed.

    Lemma sc_exp_merge : forall env H b x tx es ann k,
        k < length (fst ann) ->
        sc_var_inv' env H b x ->
        Forall (fun es => LCA.P_exps (sc_exp_inv env H b) es k) es ->
        sc_exp_inv env H b (Emerge (x, tx) es ann) k.
    Proof.
      intros * Hk Hvar Hes ss Hwc Hsem Hanon; simpl.
      inv Hwc. inv Hsem. inv Hanon.
      eapply Forall2Transpose_nth with (k0:=k) (d1:=def_stream b) (d2:=def_stream b) in H15.
      2:{ eapply Forall2Transpose_length in H15. inv H14; try congruence.
          inv H15. inv H8. inv H6.
          eapply sem_exps_numstreams in H0; eauto.
          rewrite <- H10, H0, <-length_clocksof_annots, <-H12; auto.
      }
      eapply sc_merge with (tx:=tx) in H15; eauto.
      - contradict H5.
        apply map_eq_nil, map_eq_nil in H5; subst. inv H14; auto.
      - assert (length vs = length es) as Hlen by (eapply Forall2_length in H14; eauto).
        rewrite map_length, map_length, map_map, Forall2_map_2, Hlen.
        eapply Forall2_trans_ex in H14; [|eapply H7].
        eapply Forall2_impl_In; [|eauto].
        intros * Hin1 Hin2 (?&Hin3&Ck&Sem).
        erewrite map_nth'; eauto.
        eapply Forall_forall in Hes; eauto. eapply Forall_forall in H6; eauto. eapply Forall_forall in H8; eauto.
        eapply P_exps_sc_exp_inv in Sem; eauto. 2:eapply Forall_forall in H1; eauto.
        eapply Forall_forall in Ck; [|eapply nth_In with (n:=k); rewrite <-H8; eauto].
        unfold clock_of_nclock; simpl.
        rewrite Ck; eauto.
    Qed.

    Lemma sc_exp_case : forall env H b e es d ann k,
        k < length (fst ann) ->
        sc_exp_inv env H b e 0 ->
        Forall (LiftO (LCA.P_exps (sc_exp_inv env H b) d k)
                      (fun es => LCA.P_exps (sc_exp_inv env H b) es k)) es ->
        sc_exp_inv env H b (Ecase e es d ann) k.
    Proof.
      intros * Hk He Hes ss Hwc Hsem Hanon; simpl.
      inv Hwc. inv Hsem. inv Hanon.
      eapply Forall2Transpose_nth with (k0:=k) (d1:=def_stream b) (d2:=def_stream b) in H21.
      2:{ eapply Forall2Transpose_length in H21. inv H17; try congruence.
          inv H21. rewrite <-H17.
          destruct x; simpl in *.
          - eapply sem_exps_numstreams in H0. 3:eauto.
            2:eauto.
            rewrite H0, <-length_clocksof_annots.
            rewrite <-H9; eauto.
          - inv H19. specialize (H22 eq_refl). eapply sem_exps_numstreams in H20; eauto.
            erewrite concat_length_eq. 2:eapply Forall2_impl_In; [|eauto]; intros; eapply Forall2_length; eauto.
            rewrite H20, <-length_clocksof_annots. congruence.
      }
      eapply ac_case in H21. rewrite <-H21.
      eapply He in H14; eauto.
      rewrite H5 in H14; simpl in H14.
      erewrite map_nth' with (d':=OpAux.bool_velus_type); eauto.
    Qed.

    Hypothesis Hdet : det_nodes G.

    Lemma sc_exp_app : forall env H b f es er ann k,
        wc_global G ->
        k < length ann ->
        (forall k0 : nat, k0 < length (annots es) -> LCA.P_exps (sc_exp_inv env H b) es k0) ->
        sc_exp_inv env H b (Eapp f es er ann) k.
    Proof.
      intros * HwcG Hlen Hk' ? Hwc Hsem Hanon; simpl.
      inv Hwc. inv Hsem. inv Hanon.
      eapply wc_find_node in HwcG as (G'&Wcn); eauto.
      assert (Wcn':=Wcn). destruct Wcn' as (WcIn&WcInOut&_).

      (* Arguments *)
      assert (Hse:=H3). eapply P_exps_sc_exp_inv_all in Hse; eauto.

      (* Returning aligned values *)
      assert (Hvars:=H13).
      eapply sem_exps_anon_sem_var, sc_outside_mask with (ncks:=map snd ann0) in Hvars; eauto.
      - eapply Forall2_forall2 in Hvars as [? Hck].
        repeat rewrite map_length in *.
        specialize (Hck Cbase (abstract_clock (def_stream b)) _ _ _ Hlen eq_refl eq_refl).
        rewrite map_nth, map_map in Hck; eauto.
      - change (map snd ann0) with (nclockof (Eapp f es er ann0)).
        eapply sem_exp_anon_sem_var; eauto. 1,2,3:econstructor; eauto.
      - (* Returning aligned values *)
        intros k'.
        specialize (H17 k'). inv H17. rewrite H1 in H6; inv H6.
        exists H0. repeat split; eauto.
        eapply sc_inside_mask in WcIn. 3-6:eauto. 2:eauto.
        eapply Hscnodes in H1; eauto. econstructor; eauto.
    Qed.

    Lemma sc_exp_equation : forall env H b xs es k,
        NoDupMembers env ->
        k < length xs ->
        wc_equation G env (xs, es) ->
        Sem.sem_equation G H b (xs, es) ->
        anon_sem_equation G H b (xs, es) ->
        LCA.P_exps (sc_exp_inv env H b) es k ->
        sc_var_inv' env H b (nth k xs xH).
    Proof.
      intros * Hndup Hk Hwc Hsem Hanon Hexps ? ? Hin' Hvar.
      destruct Hwc as (Hwc1&_&Hwc2). inv Hsem.
      eapply P_exps_sc_exp_inv in Hexps; eauto.
      assert (nth k (clocksof es) Cbase = ck); subst.
      { eapply Forall2_forall2 in Hwc2 as [_ HIn'].
        specialize (HIn' xH Cbase _ _ _ Hk eq_refl eq_refl).
        eapply NoDupMembers_det in Hndup; eauto. }
      assert (xs0 ≡ nth k (concat ss) (def_stream b)) as Hequiv.
      { eapply Forall2_forall2 in H6 as [_ Hvar'].
        specialize (Hvar' xH (def_stream b) _ _ _ Hk eq_refl eq_refl).
        eapply sem_var_det in Hvar'; eauto. }
      rewrite Hequiv; auto.
    Qed.

    Lemma sc_exp' : forall env H b e k,
        wc_global G ->
        wc_exp G env e ->
        k < numstreams e ->
        (forall x : ident, LCA.Is_free_left x k e -> sc_var_inv' env H b x) ->
        sc_exp_inv env H b e k.
    Proof.
      intros * Hsc Hwc Hnum Hfree.
      eapply LCA.exp_causal_ind
             with (P_exp:=sc_exp_inv _ H b); eauto.
      - apply sc_exp_const.
      - apply sc_exp_enum.
      - apply sc_exp_var.
      - apply sc_exp_unop.
      - apply sc_exp_binop.
      - apply sc_exp_fby.
      - apply sc_exp_arrow.
      - apply sc_exp_when.
      - apply sc_exp_merge.
      - apply sc_exp_case.
      - intros. eapply sc_exp_app; eauto.
    Qed.

    Lemma sem_var_refines_iff : forall dom H H' x v,
        Env.refines (@EqSt _) H H' ->
        Env.dom H dom ->
        In x dom ->
        sem_var H x v <-> sem_var H' x v.
    Proof.
      intros * Href Hdom Hin; split; intros Hvar.
      - eapply sem_var_refines; eauto.
      - eapply Env.dom_use in Hin; eauto. destruct Hin as (?&Hmaps).
        inv Hvar.
        econstructor; eauto.
        eapply Href in Hmaps as (?&?&Hmaps); subst.
        unfold Env.MapsTo in H1. rewrite Hmaps in H1. inv H1.
        now rewrite H2, H0.
    Qed.

    Lemma sem_clock_refines_iff : forall dom H H' ck bs bs',
        Env.refines (@EqSt _) H H' ->
        Env.dom H dom ->
        (forall x, Is_free_in_clock x ck -> In x dom) ->
        sem_clock H bs ck bs' <-> sem_clock H' bs ck bs'.
    Proof.
      intros * Href Hdom Hin. split. eapply sem_clock_refines; eauto.
      revert ck bs bs' H H' Href Hdom Hin.
      cofix CoFix; destruct ck; intros * Href Hdom Hin Hsem.
      - inv Hsem; constructor; auto.
      - inv Hsem.
        + econstructor; eauto.
          * eapply sem_var_refines_iff; eauto.
          * eapply CoFix. 3,4:eauto. eapply history_tl_refines; eauto.
            eapply Env.dom_map; eauto.
        + econstructor; eauto.
          * eapply sem_var_refines_iff; eauto.
          * eapply CoFix. 3,4:eauto. eapply history_tl_refines; eauto.
            eapply Env.dom_map; eauto.
        + eapply Son_abs2; eauto.
          * eapply sem_var_refines_iff; eauto.
          * eapply CoFix. 3,4:eauto. eapply history_tl_refines; eauto.
            eapply Env.dom_map; eauto.
    Qed.

    Ltac ndup_l H :=
      rewrite app_assoc in H;
      apply NoDupMembers_app_l in H; auto.
    Ltac ndup_r H :=
      rewrite Permutation_swap in H;
      apply NoDupMembers_app_r in H; auto.

    Fact sem_var_instant_mask : forall H n r k x v,
        IStr.sem_var_instant (CIStr.tr_history H n) x v ->
        IStr.sem_var_instant (CIStr.tr_history (mask_hist k r H) n) x (if (count r) # n =? k then v else absent).
    Proof.
      intros * Hsem.
      unfold IStr.sem_var_instant in *.
      setoid_rewrite Env.Props.P.F.map_o in Hsem.
      do 2 setoid_rewrite Env.Props.P.F.map_o.
      apply option_map_inv in Hsem as (?&Hfind&?); subst.
      rewrite Hfind; simpl.
      unfold tr_Stream. now rewrite maskv_nth.
    Qed.

    Lemma sem_clock_mask : forall H bs ck bs' k r,
        sem_clock H bs ck bs' ->
        sem_clock (mask_hist k r H) (maskb k r bs) ck (maskb k r bs').
    Proof.
      intros * Hck.
      rewrite sem_clock_equiv in *. unfold tr_Stream in *.
      intros n. specialize (Hck n); simpl in Hck.
      repeat rewrite maskb_nth.
      revert bs' Hck.
      induction ck; intros; inv Hck; simpl.
      - destruct (_ =? _); constructor.
      - eapply sem_var_instant_mask with (k:=k) (r:=r) in H5.
        destruct (_ =? _); constructor; eauto.
        rewrite H4. 1,2:eapply IHck; try congruence.
        erewrite <-H4; auto.
      - eapply sem_var_instant_mask with (k:=k) (r:=r) in H5.
        destruct (_ =? _); constructor; eauto.
        rewrite H4. 1,2:eapply IHck; try congruence.
        erewrite <-H4; auto.
      - eapply sem_var_instant_mask with (k:=k) (r:=r) in H5.
        destruct (_ =? _).
        + eapply IStr.Son_abs2; eauto.
          specialize (IHck (Streams.const true)).
          repeat rewrite const_nth in IHck. auto.
        + eapply IStr.Son_abs1; eauto.
          eapply IHck with (bs':=Streams.const true).
          rewrite const_nth; auto.
    Qed.

    Lemma history_mask_count : forall r H n,
        Env.Equiv eq (CIStr.tr_history (mask_hist (count r) # n r H) n) (CIStr.tr_history H n).
    Proof.
      intros *.
      rewrite Env.Equiv_orel. intros ?.
      unfold mask_hist in *.
      destruct (Env.find x (CIStr.tr_history H n)) eqn:Hfind.
      1,2:(repeat setoid_rewrite Env.Props.P.F.map_o in Hfind;
           repeat setoid_rewrite Env.Props.P.F.map_o).
      - apply option_map_inv in Hfind as (?&Hfind&?); subst.
        rewrite Hfind; simpl.
        unfold tr_Stream; rewrite maskv_nth, Nat.eqb_refl; auto.
      - apply option_map_inv_None in Hfind. rewrite Hfind; simpl; auto.
    Qed.

    Corollary sem_var_instant_mask_hist_count: forall H n r x v,
        IStr.sem_var_instant (CIStr.tr_history H n) x v <->
        IStr.sem_var_instant (CIStr.tr_history (mask_hist ((count r) # n) r H) n) x v.
    Proof.
      intros.
      split; intros; eapply IStr.sem_var_instant_morph; eauto.
      symmetry. 1,2:eapply history_mask_count.
    Qed.

    Corollary sem_var_unmask: forall r H x v,
        (forall k, sem_var (mask_hist k r H) x (maskv k r v)) ->
        sem_var H x v.
    Proof.
      setoid_rewrite sem_var_equiv.
      intros * Hsem ?.
      specialize (Hsem ((count r) # n) n).
      unfold tr_Stream in *.
      rewrite maskv_nth, Nat.eqb_refl in Hsem.
      eapply sem_var_instant_mask_hist_count; eauto.
    Qed.

    Lemma sem_clock_unmask : forall H bs ck bs' r,
        (forall k, sem_clock (mask_hist k r H) (maskb k r bs) ck (maskb k r bs')) ->
        sem_clock H bs ck bs'.
    Proof.
      setoid_rewrite sem_clock_equiv.
      intros * Hck ?.
      specialize (Hck ((count r) # n) n); simpl in Hck.
      unfold tr_Stream in *.
      repeat rewrite maskb_nth, Nat.eqb_refl in Hck.
      revert bs' Hck.
      induction ck; intros; inv Hck.
      - constructor.
      - eapply sem_var_instant_mask_hist_count in H5.
        econstructor; eauto. rewrite H4; eapply IHck; congruence.
      - eapply sem_var_instant_mask_hist_count in H5.
        econstructor; eauto. rewrite H4; eapply IHck; congruence.
      - eapply sem_var_instant_mask_hist_count in H5.
        eapply IStr.Son_abs2; eauto.
        specialize (IHck (Streams.const true)).
        repeat rewrite const_nth in IHck. auto.
    Qed.

    Lemma sc_var_inv'_mask : forall env H b x r k,
        sc_var_inv' env H b x ->
        sc_var_inv' env (mask_hist k r H) (maskb k r b) x.
    Proof.
      intros * Hinv ?? Hin Hvar.
      eapply sem_var_mask_inv in Hvar as (?&Hvar&Heq).
      rewrite Heq, ac_mask.
      eapply sem_clock_mask.
      eapply Hinv; eauto.
    Qed.

    Lemma sc_var_inv'_unmask : forall env H b x r,
      (forall k : nat, sc_var_inv' env (mask_hist k r H) (maskb k r b) x) ->
      sc_var_inv' env H b x.
    Proof.
      intros * Hinv ?? Hin Hvar.
      eapply sem_clock_unmask with (r:=r). intros k.
      rewrite <-ac_mask. eapply Hinv; eauto.
      eapply sem_var_mask; eauto.
    Qed.

    Lemma sc_block : forall env d H b x,
        wc_global G ->
        NoDupMembers (env ++ anon_in_block d) ->
        wc_env (idck env) ->
        wc_block G (idck env) d ->
        Env.dom H (map fst env) ->
        Sem.sem_block G H b d ->
        In x (vars_defined d) ->
        (forall y, LCA.depends_on x y d -> sc_var_inv' (idck env) H b y) ->
        sc_var_inv' (idck env) H b x.
    Proof.
      induction d as [(xs&es)|] using block_ind2;
        intros * Hsc Hnd Henv Hwc Hdom Hsem Hin Hvars;
        simpl in *; inv Hwc; inv Hsem.
      - (* equation *)
        assert (Hsem:=H5). eapply sem_equation_anon in H5 as (H'&Href&_&Hanon); eauto.
        eapply Sem.sem_equation_refines in Hsem; eauto.
        eapply In_nth with (d:=xH) in Hin as (?&Hlen&Hnth); subst.
        eapply sc_exp_equation in Hsem; eauto.
        + intros ?? Hin Hvar. eapply sem_clock_refines_iff; eauto.
          2:eapply Hsem; eauto using sem_var_refines.
          intros ? Hfree.
          eapply wc_env_Is_free_in_clock_In, InMembers_idck, fst_InMembers in Hfree; eauto.
        + apply NoDupMembers_app_l in Hnd. apply NoDupMembers_idck; auto.
        + assert (wl_equation G (xs, es)) as Hwl by eauto.
          destruct H1 as (Hwc&_&_).
          eapply LCA.Pexp_Pexps; eauto.
          * eapply Forall_forall. intros.
            eapply sc_exp'; eauto. eapply Forall_forall in Hwc; eauto.
          * intros * Hfree ?? Hin Hvar.
            eapply sem_clock_refines; eauto. eapply Hvars; eauto.
            -- constructor. repeat esplit; eauto.
               eapply nth_error_nth'; eauto.
            -- eapply sem_var_refines_iff; eauto.
               eapply In_idck_exists in Hin as (ty&?).
               eapply in_map_iff; exists (x, (ty, ck)); eauto.
          * inv Hwl. congruence.
      - (* reset *)
        eapply in_flat_map in Hin as (d&Hin&Hin').
        eapply Forall_forall in H; eauto. eapply Forall_forall in H3; eauto.
        assert (forall k, sc_var_inv' (idck env0) (mask_hist k r H0) (maskb k r b) x).
        { intros k. specialize (H11 k).
          eapply Forall_forall in H11; eauto.
          eapply H in H11; eauto.
          - ndup_l Hnd. eapply NoDupMembers_anon_in_block'; eauto.
          - eapply Env.dom_map; eauto.
          - intros ? Hdep.
            eapply sc_var_inv'_mask, Hvars.
            constructor. eapply Exists_exists; eauto.
        }
        eapply sc_var_inv'_unmask; eauto.
    Qed.

    Lemma sc_vars :
      forall n H b,
        wc_global G ->
        wc_node G n ->
        LCA.node_causal n ->
        Env.dom H (map fst (n_in n ++ n_vars n ++ n_out n)) ->
        Forall (sc_var_inv' (idck (n_in n ++ n_vars n ++ n_out n)) H b) (map fst (n_in n)) ->
        Forall (Sem.sem_block G H b) (n_blocks n) ->
        Forall (sc_var_inv' (idck (n_in n ++ n_vars n ++ n_out n)) H b) (map fst (n_in n ++ n_vars n ++ n_out n)).
    Proof.
      intros * HwcG Hwcn Hcau Hdom Hins Hsem.
      eapply LCA.node_causal_ind
        with (P_var:=sc_var_inv' _ H b); eauto.
      intros ? Hdef Hdep.
      eapply in_flat_map in Hdef as (d&Hin&Hin').
      eapply sc_block; eauto.
      - specialize (n_nodup n) as Hnd.
        eapply NoDupMembers_anon_in_block'; eauto.
        repeat rewrite <-app_assoc; auto.
      - destruct Hwcn as (_&_&?&_); auto.
        rewrite (Permutation_app_comm (n_vars _)); auto.
      - destruct Hwcn as (_&_&_&Hwc).
        eapply Forall_forall in Hwc; eauto.
      - eapply Forall_forall in Hsem; eauto.
      - intros ? Hdep'.
        eapply Hdep, Exists_exists; eauto.
    Qed.

    Lemma sem_clocks_det' : forall H H' b ins vins ss,
        wc_env (idck ins) ->
        Forall2 (sem_var H) (idents ins) vins ->
        Forall2 (sem_var H') (idents ins) vins ->
        Forall2 (fun xc => sem_clock H b (snd xc)) (idck ins) ss ->
        Forall2 (fun xs => sem_clock H' b (snd xs)) (idck ins) ss.
    Proof.
      intros * Hwc Hi1 Hi2 Hck.
      eapply sem_clocks_det in Hck; eauto.
      rewrite idck_app.
      apply Forall_app; split; eapply Forall_impl; eauto; intros [? ?] ?.
      1,2:eapply wc_clock_incl; eauto.
      1,2:apply incl_appl; reflexivity.
    Qed.

    Fact sem_var_In : forall H vs ss,
        Forall2 (sem_var H) vs ss ->
        Forall (fun v => Env.In v H) vs.
    Proof.
      intros. repeat rewrite_Forall_forall.
      apply In_nth with (d:=xH) in H2. destruct H2 as [n [Hn H2]].
      eapply H1 in Hn. 2,3:reflexivity.
      setoid_rewrite H2 in Hn.
      inv Hn. apply Env.find_1 in H4.
      apply Env.find_In in H4. auto.
      Unshelve. exact (Streams.const absent).
    Qed.

    Fact sem_block_In : forall H b blocks,
        Forall (Sem.sem_block G H b) blocks ->
        Forall (fun v => Env.In v H) (flat_map vars_defined blocks).
    Proof.
      induction blocks; intros Hsem; inv Hsem; simpl; auto.
      apply Forall_app; split; auto.
      eapply sem_block_sem_vars in H2 as (?&?).
      eapply sem_var_In; eauto.
    Qed.

    Lemma sem_node_restrict {prefs2} : forall (n : @node prefs2) H b xs ys,
        Forall (wc_block G (idck (n_in n ++ n_vars n ++ n_out n))) (n_blocks n) ->
        Forall2 (sem_var H) (idents (n_in n)) xs ->
        Forall2 (sem_var H) (idents (n_out n)) ys ->
        Forall (Sem.sem_block G H b) (n_blocks n) ->
        let H' := Env.restrict H (idents (n_in n ++ n_vars n ++ n_out n)) in
        Env.dom H' (idents (n_in n ++ n_vars n ++ n_out n)) /\
        Forall2 (sem_var H') (idents (n_in n)) xs /\
        Forall2 (sem_var H') (idents (n_out n)) ys /\
        Forall (Sem.sem_block G H' b) (n_blocks n).
    Proof with eauto.
      intros * Hwc Hins Houts Heqs.
      remember (Env.restrict _ _) as H'; simpl.
      repeat split.
      - subst. eapply Env.dom_lb_restrict_dom.
        apply Env.dom_lb_intro. intros x Hin.
        unfold idents in *.
        repeat rewrite map_app in Hin. repeat rewrite in_app_iff in Hin. destruct Hin as [Hin|[Hin|Hin]].
        + apply sem_var_In in Hins. rewrite Forall_forall in Hins...
        + specialize (n_defd n) as Hdef; symmetry in Hdef.
          assert (In x (flat_map vars_defined (n_blocks n))) as HIn'.
          { eapply Permutation_in in Hdef;[eauto|].
            rewrite map_app. apply in_or_app... }
          apply sem_block_In in Heqs. rewrite Forall_forall in Heqs...
        + apply sem_var_In in Houts. rewrite Forall_forall in Houts...
      - eapply Forall2_impl_In; [|eauto]; intros.
        unfold idents in H0. apply in_map_iff in H0 as ((?&?&?)&?&?); simpl in *; subst.
        eapply sem_var_restrict; eauto.
        rewrite in_app_iff; eauto.
      - eapply Forall2_impl_In; [|eauto]; intros.
        unfold idents in H0. apply in_map_iff in H0 as ((?&?&?)&?&?); simpl in *; subst.
        eapply sem_var_restrict; eauto.
        repeat rewrite in_app_iff; eauto.
      - subst. eapply sem_blocks_restrict in Heqs; eauto.
        rewrite map_fst_idck in Heqs. assumption.
    Qed.

    Lemma sc_var_inv_intro {prefs2} : forall (n : @node prefs2) H xs,
        Forall2 (sem_var H) (idents (n_in n)) xs ->
        Forall2 (fun xc => sem_clock H (clocks_of xs) (snd xc)) (idck (n_in n)) (map abstract_clock xs) ->
        Forall (sc_var_inv' (idck (n_in n ++ n_vars n ++ n_out n)) H (clocks_of xs)) (map fst (n_in n)).
    Proof.
      intros * Hvar Hclock.
      unfold idents, idck in *.
      rewrite Forall2_map_1 in Hvar. rewrite Forall2_map_1, Forall2_map_2 in Hclock.
      rewrite Forall_map.
      eapply Forall2_Forall2 in Hclock; [|eapply Hvar]. eapply Forall2_ignore2 in Hclock.
      clear - Hclock.
      eapply Forall_impl_In; [|eauto].
      intros (?&?&?) ? (?&?&?&?) ? ? ? ?; simpl in *.
      apply In_idck_exists in H4 as (?&?).
      eapply sem_var_det in H2; eauto. rewrite H2.
      specialize (node_NoDup n) as Hnd. apply fst_NoDupMembers in Hnd.
      eapply NoDupMembers_det in H4; auto. 2:eapply in_or_app; left; eauto.
      inv H4; auto.
    Qed.

    Fact wc_exp_Is_free_left : forall env e x k,
        wc_exp G env e ->
        LCA.Is_free_left x k e ->
        InMembers x env.
    Proof.
      Local Hint Resolve In_InMembers.
      Local Ltac solve_forall_exists H1 H2 H3 :=
        try eapply LCA.Is_free_left_list_Exists in H3; try destruct H3 as (?&H3);
        eapply Forall_Forall in H1; [|eapply H2];
        eapply Forall_Exists in H1; [|eapply H3];
        eapply Exists_exists in H1 as (?&?&(?&?)&?); eauto.
      induction e using exp_ind2; intros * Hwc Hfree;
        inv Hwc; inv Hfree; eauto.
      - (* binop *) destruct H1; eauto.
      - (* fby *)
        solve_forall_exists H H4 H3.
      - (* arrow *)
        destruct H3 as [Hex|Hex]; eauto.
        solve_forall_exists H H4 Hex. solve_forall_exists H0 H5 Hex.
      - (* when *)
        destruct H2 as [[? Hex]|Hex]; subst; eauto.
        solve_forall_exists H H5 Hex.
      - (* merge *)
        destruct H2 as [[? Hex]|Hex]; subst; eauto.
        eapply Exists_exists in Hex as (?&Hin&Hex).
        eapply Forall_forall in H; eauto. eapply Forall_forall in H5; eauto.
        solve_forall_exists H H5 Hex.
      - (* case *)
        destruct H3 as [[? Hex]|[Hex|Hex]]; eauto.
        + eapply Exists_exists in Hex as (?&Hin&(?&?&Hex)); subst.
          eapply Forall_forall in H; eauto; simpl in H. specialize (H8 _ Hin).
          solve_forall_exists H H8 Hex.
        + solve_forall_exists H0 H11 Hex.
      - (* app *)
        destruct H13 as [Hex|Hex]; eauto.
        solve_forall_exists H H5 Hex. solve_forall_exists H0 H6 Hex.
    Qed.

    (** After getting sc_var_inv, we can easily give an alignment lemma for expressions *)
    Lemma sc_exp_anon : forall env H b e vs,
        wc_global G ->
        NoDupMembers env ->
        sc_var_inv env H b ->

        wc_exp G env e ->
        Sem.sem_exp G H b e vs ->
        anon_sem_exp G H b e ->
        Forall2 (sem_clock H b) (clockof e) (map abstract_clock vs).
    Proof.
      intros * HwcG Hnd Hinv Hwc Hsem Hanon.
      eapply sc_var_inv_sc_var_inv' in Hinv; eauto.
      assert (forall k, k < numstreams e -> sc_exp_inv env0 H b e k); intros.
      eapply LCA.exp_causal_ind
        with (P_var:=sc_var_inv' env0 H b); eauto.
      - apply sc_exp_const.
      - apply sc_exp_enum.
      - apply sc_exp_var.
      - apply sc_exp_unop.
      - apply sc_exp_binop.
      - apply sc_exp_fby.
      - apply sc_exp_arrow.
      - apply sc_exp_when.
      - apply sc_exp_merge.
      - apply sc_exp_case.
      - intros. eapply sc_exp_app; eauto.
      - intros ? Hcau.
        eapply Forall_forall in Hinv; eauto.
        eapply wc_exp_Is_free_left in Hcau; eauto.
        rewrite <- fst_InMembers; eauto.
      - assert (length vs = numstreams e) as Hlen'.
        { eapply sem_exp_numstreams in Hsem; eauto. }
        eapply Forall2_forall2; split.
        + rewrite map_length.
          rewrite length_clockof_numstreams; auto.
        + intros ? ? ? ? ? Hlen Hnth1 Hnth2; subst.
          rewrite length_clockof_numstreams in Hlen.
          specialize (H0 _ Hlen _ Hwc Hsem).
          rewrite nth_indep with (d':=Cbase). 2:rewrite length_clockof_numstreams; auto.
          erewrite map_nth'; eauto. congruence.
    Qed.

    Corollary sc_exps_anon : forall env H b es vss,
        wc_global G ->
        NoDupMembers env ->
        sc_var_inv env H b ->

        Forall (wc_exp G env) es ->
        Forall2 (Sem.sem_exp G H b) es vss ->
        Forall (anon_sem_exp G H b) es ->
        Forall2 (sem_clock H b) (clocksof es) (map abstract_clock (concat vss)).
    Proof.
      intros * HwcG Hnd Hsc Hwc Hsem Hanon.
      unfold clocksof.
      rewrite Forall2_map_2, flat_map_concat_map.
      apply Forall2_concat. rewrite Forall2_map_1.
      eapply Forall2_impl_In; [|eauto]; intros.
      eapply sc_exp_anon in H2; eauto. 2,3:eapply Forall_forall; eauto.
      rewrite Forall2_map_2 in H2; eauto.
    Qed.
  End sc_inv.

  Lemma sc_var_inv_mask : forall env H b r k,
      sc_var_inv env H b ->
      sc_var_inv env (mask_hist k r H) (maskb k r b).
  Proof.
    intros * Hinv.
    eapply Forall_impl; [|eauto]. intros (?&?) (?&Hvar&Hck).
    eapply sem_var_mask in Hvar. eapply sem_clock_mask in Hck.
    exists (maskv k r x). split; eauto. rewrite ac_mask; eauto.
  Qed.

  Lemma sc_var_inv_unmask : forall env H b r,
      (forall k, sc_var_inv env (mask_hist k r H) (maskb k r b)) ->
      sc_var_inv env H b.
  Proof.
    intros * Hinv.
    eapply Forall_forall; intros (?&?) Hin.
    specialize (Hinv 0) as Hinv0.
    eapply Forall_forall in Hinv0; eauto. destruct Hinv0 as (?&Hvar0&_).
    eapply sem_var_mask_inv in Hvar0 as (vs&Hvar0&Heq0).
    exists vs. split; auto.
    eapply sem_clock_unmask; intros k. rewrite <-ac_mask.
    specialize (Hinv k) as Hinvk.
    eapply Forall_forall in Hinvk; eauto. destruct Hinvk as (?&Hvark&Hckk).
    eapply sem_var_mask_inv in Hvark as (vs'&Hvark&Heqk).
    eapply sem_var_det in Hvar0; eauto.
    rewrite <-Hvar0, <-Heqk; auto.
  Qed.

  Fact sc_var_inv_refines : forall env H H' b,
      Env.refines (@EqSt _) H H' ->
      sc_var_inv env H b ->
      sc_var_inv env H' b.
  Proof.
    intros * Href Hsc.
    unfold sc_var_inv in *.
    eapply Forall_impl; [|eauto].
    intros (?&?) (?&Hvar&Hck).
    exists x. split.
    - eapply sem_var_refines; eauto.
    - eapply sem_clock_refines; eauto.
  Qed.

  Lemma sc_var_inv_slower_hist : forall env H b,
      sc_var_inv env H b ->
      Env.dom H (map fst env) ->
      slower_hist H b.
  Proof.
    intros * Hsc Hdom ?? Hfind.
    assert (exists ck, In (x, ck) env0) as (?&Hin).
    { eapply Env.find_In, Env.dom_use in Hfind; eauto.
      eapply in_map_iff in Hfind as ((?&?)&?&?); subst; eauto. }
    eapply Forall_forall in Hsc; eauto.
    simpl in *. destruct Hsc as (?&Hsem&Hck).
    eapply sem_var_det in Hsem.
    2:{ econstructor; eauto. reflexivity. }
    rewrite <-Hsem in Hck.
    eapply sc_slower; eauto. eapply ac_aligned.
  Qed.

  (** Second step of the proof:
      Give clocked semantics for expressions, equations and blocks,
      given that all named streams are aligned with their clocks
   *)
  Section sem_ck.
    Context {prefs : PS.t}.
    Variable (G : @global prefs).

    Hypothesis HwcG : wc_global G.

    Hypothesis Hdet : det_nodes G.

    Hypothesis Hnode : forall f ins outs,
        sem_node G f ins outs ->
        sem_clock_inputs G f ins ->
        sem_node_ck G f ins outs.

    Lemma sem_exp_anon_sem_exp_clocked : forall env H bs e vs,
        NoDupMembers env ->
        sc_var_inv env H bs ->
        wc_exp G env e ->
        Sem.sem_exp G H bs e vs ->
        anon_sem_exp G H bs e ->
        sem_exp_ck G H bs e vs.
    Proof.
      induction e using exp_ind2; intros * Hnd Hsc Hwc Hsem Hanon;
        inv Hwc; inv Hsem; inv Hanon;
          econstructor; eauto.
      1-6,8-10:(eapply Forall2_impl_In; [|eauto]; intros;
                rewrite Forall_forall in *; eauto).
      - (* merge *)
        eapply Forall2_impl_In; [|eauto]; intros.
        specialize (H0 _ H1). specialize (H2 _ H1). specialize (H6 _ H1).
        rewrite Forall_forall in *; eauto.
      - (* case *)
        clear H21.
        eapply Forall2_impl_In; [|eauto]; intros; subst.
        eapply Forall_forall in H0; eauto; simpl in *.
        specialize (H9 _ H2).
        eapply Forall_forall in H17; eauto. specialize (H17 _ eq_refl).
        eapply Forall2_impl_In; [|eauto]; intros; subst.
        rewrite Forall_forall in *; eauto.
      - (* app *)
        intros k. eapply Hnode; eauto.
        specialize (H19 k). inv H19. rewrite H8 in H3; inv H3.
        repeat (esplit; eauto).
        eapply sc_inside_mask with (es0:=es); eauto.
        + eapply sem_exps_anon_sem_var; eauto.
        + eapply wc_find_node in HwcG as (?&?&?); eauto.
        + eapply sc_exps_anon; eauto.
      - (* clocked_app *)
        assert (Forall2 (fun '(_, o) vs => LiftO True (fun x => sem_var H x vs) o) (nclockof (Eapp f es er a)) vs) as Hvars.
        { eapply sem_exp_anon_sem_var; eauto. 1,2,3:econstructor; eauto. }
        unfold anon_app, clocked_app in *.
        assert (Forall2 (sem_clock H bs) (map fst (map snd a)) (map abstract_clock vs)) as Hckout.
        { eapply sc_outside_mask with (es0:=es); eauto.
          eapply sem_exps_anon_sem_var; eauto.
          1,2:eapply wc_find_node in HwcG as (?&?&?&?); eauto.
          - eapply sc_exps_anon; eauto.
          - intros k'.
            specialize (H19 k'). inv H19. rewrite H3 in H8; inv H8.
            exists H2. repeat split; eauto.
            eapply sc_inside_mask in H9. 5:eauto.
            1,3:eapply wc_find_node in HwcG as (?&?&?); eauto.
            + eapply Hscnodes in H9; eauto. 1,2:econstructor; eauto.
            + eapply sem_exps_anon_sem_var; eauto.
            + eapply sc_exps_anon; eauto.
        }
        rewrite 2 Forall2_map_1, Forall2_map_2 in Hckout.
        simpl in Hvars. rewrite Forall2_map_1 in Hvars.
        eapply Forall2_Forall2 in Hvars; [|eauto]. clear Hckout.
        eapply Forall2_impl_In; [|eauto]. intros (?&?&[|]) ? ? ? (Hclock&Hvar); simpl in *; auto.
    Qed.

    Corollary sem_equation_anon_sem_equation_clocked : forall env H bs equ,
        NoDupMembers env ->
        sc_var_inv env H bs ->
        wc_equation G env equ ->
        Sem.sem_equation G H bs equ ->
        anon_sem_equation G H bs equ ->
        sem_equation_ck G H bs equ.
    Proof.
      intros * Hnd Hsc Hwc Hsem Hanon.
      inv Hsem. inv Hwc.
      econstructor; eauto.
      eapply Forall2_impl_In; [|eauto]; intros.
      eapply sem_exp_anon_sem_exp_clocked; eauto. 1,2:eapply Forall_forall; eauto.
    Qed.

    Hint Resolve Env.union_refines2 Env.union_dom Env.adds_opt'_refines Env.adds_opt'_dom
         EqStrel EqStrel_Reflexive clocked_app_refines.

    Lemma sc_var_inv_fresh_in : forall H bs e vs,
        sem_exp_ck G H bs e vs ->
        sc_var_inv (idck (fresh_in e)) H bs.
    Proof.
      unfold sc_var_inv, idck.
      setoid_rewrite Forall_map.
      Local Ltac solve_Forall Hf Hsem :=
        rewrite flat_map_concat_map;
        apply Forall_concat, Forall_map;
        eapply Forall2_ignore2 in Hsem;
        eapply Forall_impl_In; [|eapply Hf]; intros;
        eapply Forall_forall in Hsem as (?&?&?); eauto.

      induction e using exp_ind2; intros * Hsem; inv Hsem;
        simpl; repeat rewrite Forall_app; eauto.
      - (* fby *)
        split.
        + solve_Forall H0 H8.
        + solve_Forall H1 H10.
      - (* arrow *)
        split.
        + solve_Forall H0 H8.
        + solve_Forall H1 H10.
      - (* when *)
        solve_Forall H0 H9.
      - (* merge *)
        solve_Forall H0 H9.
        solve_Forall H2 H4.
      - (* case *)
        repeat split; eauto.
        + solve_Forall H0 H10.
          destruct a0; simpl in *; auto.
          specialize (H5 _ eq_refl).
          solve_Forall H3 H5.
        + solve_Forall H1 H13.
      - (* app *)
        repeat split.
        + solve_Forall H0 H7.
        + solve_Forall H1 H10.
        + unfold clocked_app in H14.
          clear - H14.
          induction H14; simpl; auto.
          destruct x as (?&?&[|]); simpl; auto.
          constructor; simpl in *; eauto.
    Qed.

    Corollary sc_var_inv_anon_in : forall H bs e vs,
        sem_exp_ck G H bs e vs ->
        sc_var_inv (idck (anon_in e)) H bs.
    Proof.
      unfold sc_var_inv, idck.
      intros * Hsem.
      destruct e. 1-10:eapply sc_var_inv_fresh_in; eauto.
      inv Hsem.
      simpl. rewrite Forall_map, Forall_app.
      unfold fresh_ins. repeat rewrite flat_map_concat_map.
      split; apply Forall_concat, Forall_map, Forall_forall; intros.
      - eapply Forall2_ignore2, Forall_forall in H5 as (?&?&Hsem); eauto.
        eapply sc_var_inv_fresh_in in Hsem; eauto.
        unfold sc_var_inv, idck in *. now rewrite Forall_map in Hsem.
      - eapply Forall2_ignore2, Forall_forall in H8 as (?&?&Hsem); eauto.
        eapply sc_var_inv_fresh_in in Hsem; eauto.
        unfold sc_var_inv, idck in *. now rewrite Forall_map in Hsem.
    Qed.

    Corollary sc_var_inv_anon_in_eq : forall H bs equ,
        sem_equation_ck G H bs equ ->
        sc_var_inv (idck (anon_in_eq equ)) H bs.
    Proof.
      intros * Hsem. inv Hsem.
      unfold sc_var_inv, idck, anon_in_eq, anon_ins.
      rewrite flat_map_concat_map.
      apply Forall_map, Forall_concat, Forall_map.
      eapply Forall_forall; intros.
      eapply Forall2_ignore2, Forall_forall in H1 as (?&?&Hsem); eauto.
      eapply sc_var_inv_anon_in in Hsem.
      unfold sc_var_inv, idck in *. now rewrite Forall_map in Hsem.
    Qed.

    Lemma sc_var_inv_anon_in_block : forall bck H bs,
        sem_block_ck G H bs bck ->
        sc_var_inv (idck (anon_in_block bck)) H bs.
    Proof.
      unfold sc_var_inv.
      induction bck using block_ind2;
        intros * Hsem; inv Hsem; simpl.
      - (* equation *)
        eapply sc_var_inv_anon_in_eq; eauto.
      - (* reset *)
        rewrite idck_app, Forall_app; split.
        + eapply sc_var_inv_unmask; intros k. specialize (H8 k).
          unfold sc_var_inv, idck.
          rewrite Forall_map, flat_map_concat_map.
          apply Forall_concat, Forall_map.
          eapply Forall_impl_In; [|eapply H]; intros; simpl in *.
          setoid_rewrite Forall_map in H2. eapply Forall_impl; [|eapply H2].
          2:eapply Forall_forall in H8; eauto.
          intros (?&?&?) ?; eauto.
        + eapply sc_var_inv_fresh_in in H4; eauto.
    Qed.

    Corollary sc_var_inv_anon_in_blocks : forall H bs bcks,
        Forall (sem_block_ck G H bs) bcks ->
        sc_var_inv (idck (flat_map anon_in_block bcks)) H bs.
    Proof.
      intros * Hsem.
      rewrite flat_map_concat_map.
      eapply Forall_map, Forall_concat, Forall_map.
      eapply Forall_impl; [|eauto]; intros.
      eapply sc_var_inv_anon_in_block, Forall_map in H0; eauto.
    Qed.

    Fact sem_blocks_sem_blocks_clocked : forall env H bs bcks,
      Forall
        (fun bck => forall H bs,
         NoDupMembers (env ++ anon_in_block bck) ->
         Env.dom H (map fst env) ->
         sc_var_inv (idck env) H bs ->
         wc_block G (idck env) bck ->
         Sem.sem_block G H bs bck ->
         exists H',
           Env.refines (EqSt (A:=svalue)) H H' /\
           Env.dom H' (map fst env ++ map fst (anon_in_block bck)) /\
           sem_block_ck G H' bs bck) bcks ->
      NoDupMembers (env ++ flat_map anon_in_block bcks) ->
      Env.dom H (map fst env) ->
      sc_var_inv (idck env) H bs ->
      Forall (wc_block G (idck env)) bcks ->
      Forall (sem_block G H bs) bcks ->
      exists H',
        Env.refines (@EqSt _) H H' /\
        Env.dom H' (map fst env ++ map fst (flat_map anon_in_block bcks)) /\
        Forall (sem_block_ck G H' bs) bcks.
    Proof.
      induction bcks; intros * Hf Hnd Hdom Hsc Hwc Hsem;
        inv Hwc; inv Hsem; inv Hf.
      - simpl_ndup Hnd. exists H; auto.
      - unfold anon_in_block in Hnd; simpl_ndup Hnd.
        eapply IHbcks in H7 as (H'2&Hr2&Hd2&Hs2); eauto. 2:ndup_r Hnd. clear IHbcks.
        eapply H6 in H4 as (H'1&Hr1&Hd1&Hs1); eauto. 2:ndup_l Hnd. clear H6.
        exists (Env.union H'1 H'2). repeat split; eauto.
        apply NoDupMembers_app_r, fst_NoDupMembers in Hnd. rewrite map_app in Hnd.
        constructor; eauto. 2:eapply Forall_impl; [|eauto]; intros.
        1,2:eapply sem_block_refines. 2,4:eauto.
        eapply Env.union_refines3 in Hdom; eauto.
        eapply Env.union_refines4 in Hdom; eauto.
    Qed.

    Lemma sem_block_sem_block_clocked : forall env bck H bs,
        NoDupMembers (env ++ anon_in_block bck) ->
        Env.dom H (map fst env) ->
        sc_var_inv (idck env) H bs ->
        wc_block G (idck env) bck ->
        sem_block G H bs bck ->
        exists H',
          Env.refines (@EqSt _) H H' /\
          Env.dom H' (map fst env ++ map fst (anon_in_block bck)) /\
          sem_block_ck G H' bs bck.
    Proof.
      induction bck using block_ind2;
        intros * Hnd Hdom Hsc Hwc Hsem; inv Hsem; inv Hwc; simpl_ndup Hnd.
      - (* Beq *)
        assert (Hsem:=H4). eapply sem_equation_anon in H4 as (H'&Href&Hdom'&Hanon); eauto.
        exists H'. repeat (split; auto).
        econstructor; eauto.
        eapply sem_equation_anon_sem_equation_clocked; eauto using Sem.sem_equation_refines, sc_var_inv_refines.
        eapply NoDupMembers_idck, NoDupMembers_app_l; eauto.
      - (* Breset *)
        assert (forall k, exists H'k,
                     Env.refines (@EqSt _) (mask_hist k r H0) (mask_hist k r H'k) /\
                     Env.dom (mask_hist k r H'k) (map fst env0 ++ map fst (flat_map anon_in_block blocks)) /\
                     Forall (sem_block_ck G (mask_hist k r H'k) (maskb k r bs)) blocks) as Hbcks.
        { intros k.
          eapply sem_blocks_sem_blocks_clocked with (H:=mask_hist k r H0) in H as (H'&Href&Hdom'&Hsem'); eauto.
          2:ndup_l Hnd.
          2:eapply Env.dom_map; eauto.
          2:eapply sc_var_inv_mask; eauto.
          assert (slower_hist H' (maskb k r bs)) as Hslow.
          { eapply sc_var_inv_slower_hist.
            2:rewrite <-map_app, <-map_fst_idck in Hdom'; eauto.
            rewrite idck_app.
            eapply sc_var_inv_mask, sc_var_inv_refines in Hsc; eauto.
            apply Forall_app; split; auto.
            setoid_rewrite Forall_map. rewrite flat_map_concat_map. apply Forall_concat, Forall_map.
            eapply Forall_impl_In; [|eauto]; intros.
            apply sc_var_inv_anon_in_block in H1.
            unfold sc_var_inv, idck in *. now rewrite Forall_map in H1.
          }
          eapply slower_mask_hist in Hslow.
          exists H'. repeat (split; auto).
          3:(eapply Forall_impl; [|eauto]; intros;
             eapply sem_block_refines; [|eauto]).
          1-3:rewrite <- Hslow; auto.
        }
        eapply consolidate_mask_hist
          with (P := fun k H'k => Env.refines (@EqSt _) (mask_hist k r H0) H'k /\
                               Env.dom H'k (map fst env0 ++ map fst (flat_map anon_in_block blocks)) /\
                               Forall (sem_block_ck G H'k (maskb k r bs)) blocks)
          in Hbcks as (H'1&HH').
        2:{ intros ????? Heq (?&?&?); subst. repeat (split; auto).
            1-2:rewrite <-Heq; auto.
            eapply Forall_impl; [|eauto]; intros.
            eapply sem_block_refines; [|eauto]. rewrite <-Heq; auto.
        }
        2:{ intros ????? (_&Hdom1&_) (_&Hdom2&_) Hdom'.
            eapply Env.dom_intro; intros.
            eapply Env.dom_use in Hdom1. eapply Env.dom_use in Hdom2. eapply Env.dom_use in Hdom'.
            rewrite Hdom2, <-Hdom1; eauto.
        }
        assert (Env.refines (@EqSt _) H0 H'1) as Href1.
        { eapply refines_unmask; intros.
          specialize (HH' k) as (?&_); eauto. }
        assert (Env.dom H'1 (map fst env0 ++ map fst (flat_map anon_in_block blocks))) as Hdom1.
        { specialize (HH' 0) as (_&Hdom1&_). setoid_rewrite Env.dom_map in Hdom1; eauto. }
        assert (Hsem2:=H4). eapply sem_exp_fresh in H4 as (H'2&Href2&Hdom2&Hanon2); eauto. 2:ndup_r Hnd.
        exists (Env.union H'1 H'2). repeat split; auto.
        econstructor; eauto.
        + eapply sem_exp_anon_sem_exp_clocked; eauto using sc_var_inv_refines.
          * eapply NoDupMembers_idck, NoDupMembers_app_l; eauto.
          * eapply Sem.sem_exp_refines; [|eauto]; eauto.
          * eapply anon_sem_exp_refines; [|eauto].
            eapply Env.union_refines4 in Hdom; eauto.
            apply NoDupMembers_app_r, fst_NoDupMembers in Hnd. now rewrite map_app in Hnd.
        + intros k.
          specialize (HH' k) as (_&_&Hsem').
          eapply Forall_impl; [|eapply Hsem']; intros.
          eapply sem_block_refines; [|eauto].
          eapply refines_mask.
          eapply Env.union_refines3 in Hdom; eauto.
          apply NoDupMembers_app_r, fst_NoDupMembers in Hnd. now rewrite map_app in Hnd.
    Qed.

  End sem_ck.

  Theorem sem_node_sem_node_ck {prefs} :
    forall (G : @global prefs),
      Forall LCA.node_causal (nodes G) ->
      Ordered_nodes G ->
      wc_global G ->
      forall f ins outs,
        Sem.sem_node G f ins outs ->
        sem_clock_inputs G f ins ->
        sem_node_ck G f ins outs.
  Proof with eauto.
    intros (enums&nodes).
    induction nodes; intros Hcaus Hord Hwc ??? Hsem Hckins. now inversion Hsem.
    assert (Hsem' := Hsem).
    inversion_clear Hsem' as [? ? ? ? ? ? Hfind Hins Houts Heqs Hbk].
    pose proof (Lord.find_node_not_Is_node_in _ _ _ Hord Hfind) as Hnini.
    simpl in Hfind. destruct (ident_eq_dec (n_name a) f).
    - destruct Hckins as (?&?&Hfind'&Hins'&Hscin).
      rewrite find_node_now in Hfind'; auto. inv Hfind'.
      rewrite find_node_now in Hfind; auto. inv Hfind.
      eapply Sem.sem_blocks_cons in Heqs; eauto.
      assert (Hord':=Hord). inversion_clear Hord' as [|? ? Hord'' Hnneqs Hnn].
      inversion_clear Hwc as [|?? (Hwcn&_) Hwcg].
      inv Hcaus.
      assert (Hwcn':=Hwcn). destruct Hwcn' as (?&?&_&?).

      (* sem_clock H0 -> sem_clock H *)
      eapply sem_clocks_det' in Hscin; eauto. clear x Hins'.

      (* restrict H *)
      eapply sem_node_restrict in Heqs as (Hdom&Hins'&Houts'&Heqs'); eauto.
      remember (Env.restrict H (idents (n_in n ++ n_vars n ++ n_out n))) as H'.
      eapply sem_clocks_det with (ins:=n_out n) in Hscin; eauto. 2:rewrite Permutation_app_comm; eauto.
      clear H HeqH' Hins Houts.

      (* sc_var_inv H *)
      assert (wc_global (Global enums nodes0)) as Hvars by eauto.
      eapply sc_vars in Hvars; eauto.
      2:{ eapply det_global_n; eauto. }
      2:{ eapply sc_var_inv_intro; eauto. }
      rewrite <-map_fst_idck in Hvars. eapply sc_var_inv'_sc_var_inv in Hvars.
      2:{ rewrite map_fst_idck. eapply Forall_forall; intros.
          eapply Env.dom_use in H; eauto.
          eapply Env.In_find in H as (v&Hfind).
          exists v. esplit; eauto. reflexivity. }

      (* sem_node_ck *)
      eapply sem_blocks_sem_blocks_clocked in Heqs' as (H''&Href'&Hdom'&Hsem'); eauto.
      2:{ eapply Forall_forall; intros.
          eapply sem_block_sem_block_clocked; eauto using det_global_n. }
      2:{ repeat rewrite <-app_assoc. apply n_nodup. }
      eapply Snode with (H:=H''); eauto.
      + rewrite find_node_now; auto.
      + eapply Forall2_impl_In; [|eauto]; intros.
        eapply sem_var_refines; eauto.
      + eapply Forall2_impl_In; [|eauto]; intros.
        eapply sem_var_refines; eauto.
      + eapply sem_blocks_ck_cons'; eauto.
      + unfold clocked_node. split.
        * rewrite map_app; auto.
        * eapply sc_var_inv_refines; eauto.

    - rewrite find_node_other in Hfind; eauto.
      eapply Sem.sem_node_cons in Hsem; auto.
      assert (Hord':=Hord). rewrite cons_is_app in Hord'.
      inv Hord'. inv Hwc. inv Hcaus. eapply IHnodes in Hsem; eauto.
      eapply sem_node_ck_cons'; eauto.
      eapply sem_clock_inputs_cons; eauto.
  Qed.

  (** ** Properties
      After getting sem_exp_clocked, we can give a direct alignment lemma for expressions *)

  Hint Constructors anon_sem_exp.

  Lemma sem_exp_ck_sem_var {prefs} :
    forall (G: @global prefs) env H b e vs,
      wc_exp G env e ->
      sem_exp_ck G H b e vs ->
      Forall2 (fun '(_, o) s => LiftO True (fun x : ident => sem_var H x s) o) (nclockof e) vs.
  Proof.
    intros * Hwc Hsem.
    assert (length vs = length (nclockof e)) as Hlen.
    { rewrite length_nclockof_numstreams. eapply sem_exp_numstreams, sem_exp_ck_sem_exp; eauto. }
    inv Hwc; inv Hsem; simpl in *.
    1-6:constructor; simpl; auto.
    - (* fby *)
      clear - Hlen H4. rewrite map_length in Hlen; symmetry in Hlen.
      eapply Forall2_ignore2' in H4; eauto.
      clear Hlen. induction H4; simpl; constructor; auto.
      destruct x as [? [? [?|]]]; simpl; auto. inv H0.
    - (* arrow *)
      clear - Hlen H4. rewrite map_length in Hlen; symmetry in Hlen.
      eapply Forall2_ignore2' in H4; eauto.
      clear Hlen. induction H4; simpl; constructor; auto.
      destruct x as [? [? [?|]]]; simpl; auto. inv H0.
    - (* when *)
      rewrite map_length in Hlen.
      rewrite Forall2_map_1; simpl. apply Forall2_forall2; split; auto.
    - (* merge *)
      rewrite map_length in Hlen.
      rewrite Forall2_map_1; simpl. apply Forall2_forall2; split; auto.
    - (* case *)
      rewrite map_length in Hlen.
      rewrite Forall2_map_1; simpl. apply Forall2_forall2; split; auto.
    - (* app *)
      rewrite Forall2_map_1.
      eapply Forall2_impl_In; eauto. intros (?&?&?) ? _ _ Hv.
      destruct o; simpl in *; auto. now destruct Hv.
  Qed.

  Corollary sem_exps_ck_sem_var {prefs} :
    forall (G: @global prefs) env H b es vs,
      Forall (wc_exp G env) es ->
      Forall2 (sem_exp_ck G H b) es vs ->
      Forall2 (fun '(_, o) s => LiftO True (fun x : ident => sem_var H x s) o) (nclocksof es) (concat vs).
  Proof.
    induction es; intros * Hwc Hsem; inv Hwc; inv Hsem; simpl; auto.
    apply Forall2_app; auto.
    eapply sem_exp_ck_sem_var; eauto.
  Qed.

  Lemma sc_outside_mask' {prefs} :
    forall (G: @global prefs) f n H b env ncks es rs ss vs bck sub,
      wc_global G ->
      find_node f G = Some n ->
      Forall (wc_exp G env) es ->
      Forall2 (sem_exp_ck G H b) es ss ->
      (forall k, sem_node_ck G f (map (maskv k rs) (concat ss)) (map (maskv k rs) vs)) ->
      Forall2 (fun '(_, o) (s : Stream svalue) => LiftO True (fun x0 : ident => sem_var H x0 s) o) ncks vs ->
      Forall2 (sem_clock H b) (clocksof es) (map abstract_clock (concat ss)) ->
      Forall2 (WellInstantiated bck sub) (idck (n_in n)) (nclocksof es) ->
      Forall2 (WellInstantiated bck sub) (idck (n_out n)) ncks ->
      Forall2 (sem_clock H b) (map fst ncks) (map abstract_clock vs).
  Proof.
    intros * HwcG Hfind Hwc Hseme Hsem Hvars Hcki Hwi Hwo.
    eapply sc_outside_mask with (rs0:=rs) (es0:=es); eauto.
    2,3:eapply wc_find_node in HwcG as (?&?&?&?); eauto.
    - eapply sem_exps_ck_sem_var; eauto.
    - intros k.
      specialize (Hsem k). inv Hsem. rewrite Hfind in H1; inv H1.
      exists H0. repeat split; eauto.
      destruct H6 as (?&Hinv). clear - H3 Hinv. unfold sc_var_inv in Hinv.
      unfold idents, idck in *.
      rewrite Forall2_map_1, Forall2_map_2. rewrite Forall2_map_1 in H3.
      eapply Forall2_impl_In; [|eauto]; intros (?&?&?) ? Hin _ Hvar.
      eapply Forall_map, Forall_forall in Hinv; eauto using in_or_app.
      destruct Hinv as (?&Hvar'&Hck).
      eapply sem_var_det in Hvar; eauto.
      rewrite <-Hvar; eauto.
  Qed.

  Fact sc_exps' {prefs} : forall (G : @global prefs) H b env es ss,
      Forall
         (fun e => forall vs,
              wc_exp G env e ->
              sem_exp_ck G H b e vs ->
              Forall2 (sem_clock H b) (clockof e) (map abstract_clock vs)) es ->

      Forall (wc_exp G env) es ->
      Forall2 (sem_exp_ck G H b) es ss ->
      Forall2 (sem_clock H b) (clocksof es) (map abstract_clock (concat ss)).
  Proof.
    intros * Hf Hwc Hsem.
    assert (length es = length ss) as Hlength by (eapply Forall2_length in Hsem; eauto).
    eapply Forall2_ignore2' in Hwc; eauto.
    eapply Forall2_Forall2 in Hsem; eauto. clear Hwc.
    unfold clocksof. rewrite flat_map_concat_map, Forall2_map_2.
    apply Forall2_concat. rewrite Forall2_map_1.
    eapply Forall2_impl_In; eauto. clear Hsem.
    intros ? ? ? ? (Hwc&Hsem).
    eapply Forall_forall in Hf; eauto.
    setoid_rewrite Forall2_map_2 in Hf; eauto.
  Qed.

  Lemma sc_exp {prefs} : forall (G : @global prefs) env H b e vs,
      wc_global G ->
      sc_var_inv env H b ->
      wc_exp G env e ->
      sem_exp_ck G H b e vs ->
      Forall2 (sem_clock H b) (clockof e) (map abstract_clock vs).
  Proof.
    intros * HwcG Hinv. revert vs.
    induction e using exp_ind2; intros * Hwc Hsem;
      inv Hwc; inv Hsem; simpl.
    - (* const *)
      constructor; auto.
      rewrite H4, ac_const. now constructor.
    - (* enum *)
      constructor; auto.
      rewrite H6, ac_enum. now constructor.
    - (* var *)
      constructor; auto.
      eapply Forall_forall in Hinv; eauto. destruct Hinv as (?&Hvar&Hsem).
      eapply sem_var_det in H7; eauto. rewrite <-H7; auto.
    - (* var *)
      constructor; auto.
      eapply Forall_forall in Hinv; eauto. destruct Hinv as (?&Hvar&Hsem).
      eapply sem_var_det in H7; eauto. rewrite <-H7; auto.
    - (* unop *)
      eapply IHe in H8; eauto. rewrite H4 in H8; simpl in H8.
      rewrite <-ac_lift1; eauto.
    - (* binop *)
      eapply IHe1 in H9; eauto. rewrite H6 in H9; simpl in H9.
      rewrite <-ac_lift2; eauto.
    - (* fby *)
      rewrite Forall2_eq in H7. rewrite H7.
      eapply sc_exps' in H0; eauto.
      clear - H16 H0. revert H0. generalize (clocksof e0s).
      induction H16; intros ? Hsem; simpl in *; inv Hsem; constructor; auto.
      rewrite <- ac_fby1; eauto.
    - (* arrow *)
      rewrite Forall2_eq in H7. rewrite H7.
      eapply sc_exps' in H0; eauto.
      clear - H16 H0. revert H0. generalize (clocksof e0s).
      induction H16; intros ? Hsem; simpl in *; inv Hsem; constructor; auto.
      rewrite <- ac_arrow1; eauto.
    - (* when *)
      eapply sc_exps' in H0; eauto.
      erewrite Forall_eq with (l2:=clocksof es) in H0; eauto.
      unfold clock_of_nclock, stripname; simpl.
      clear - H14 H15 H0. revert tys H0.
      repeat setoid_rewrite Forall2_map_1.
      induction H15; intros * Hsem; simpl in *; inv Hsem; constructor; eauto.
      eapply sc_when; eauto.
    - (* merge *)
      rewrite Forall2_map_1, Forall2_map_2.
      eapply Forall2_forall2. split.
      { inv H8; try congruence. simpl in *.
        rewrite H1. inv H15. inv H6.
        eapply sem_exps_ck_sem_exps, sem_exps_numstreams in H9; eauto.
        rewrite length_clocksof_annots; auto.
        eapply Forall2Transpose_length in H16. simpl in H16; inv H16.
        congruence.
      }
      intros; subst.
      { eapply Forall2Transpose_nth with (k:=n) (d1:=b0) (d2:=b0) in H16.
        2:{ eapply Forall2Transpose_length in H16. inv H15; try congruence.
            inv H16. inv H8. inv H6.
            eapply sem_exps_ck_sem_exps, sem_exps_numstreams in H2; eauto.
            rewrite <- H11, H2, <-length_clocksof_annots, <-H13; auto.
        }
        eapply sc_merge with (tx:=tx) in H16; eauto.
        - contradict H5.
          apply map_eq_nil, map_eq_nil in H5; subst. inv H15; auto.
        - assert (length vs0 = length es) as Hlen by (eapply Forall2_length in H15; eauto).
          rewrite map_length, map_length, map_map, Forall2_map_2, Hlen.
          eapply Forall2_trans_ex in H15; [|eapply H7].
          eapply Forall2_impl_In; [|eauto].
          intros * Hin1 Hin2 (?&Hin3&Ck&Sem).
          eapply Forall_forall in H0; eauto. eapply Forall_forall in H6; eauto. eapply Forall_forall in H8; eauto.
          eapply sc_exps' in H0; eauto.
          eapply Forall2_forall2 in H0 as (_&?). eapply H0 with (a:=Cbase); eauto. 3:eapply map_nth; eauto.
          2:eapply Forall_forall in Ck; [|eapply nth_In with (n:=n); eauto]; [symmetry; eapply Ck|].
          1,2:congruence.
      }
    - (* case *)
      rewrite Forall2_map_1, Forall2_map_2.
      eapply Forall2_forall2. split.
      { destruct es as [|[|]]; try congruence.
        - inv H19. erewrite H11; eauto with datatypes.
          rewrite length_clocksof_annots; auto.
          eapply sem_exps_ck_sem_exps, sem_exps_numstreams in H4. 3:eauto. 2:eauto with datatypes.
          eapply Forall2Transpose_length in H23. simpl in H23; inv H23.
          congruence.
        - inv H21. erewrite H14.
          rewrite length_clocksof_annots; auto.
          eapply sem_exps_ck_sem_exps, sem_exps_numstreams in H22; eauto.
          specialize (H4 eq_refl). eapply Forall2_concat, Forall2_length in H4.
          eapply Forall2Transpose_length in H23. simpl in H23; inv H23.
          congruence.
      }
      intros; subst.
      { eapply Forall2Transpose_nth with (k:=n) (d1:=b0) (d2:=b0) in H23.
        2:{ eapply Forall2Transpose_length in H23. inv H19; try congruence.
            inv H23. rewrite <-H17.
            destruct x; simpl in *.
            - eapply sem_exps_ck_sem_exps, sem_exps_numstreams in H3. 3:eauto.
              2:eauto.
              rewrite H3, <-length_clocksof_annots.
              rewrite <-H11; eauto.
            - inv H21. specialize (H20 eq_refl). eapply sem_exps_ck_sem_exps, sem_exps_numstreams in H22; eauto.
              erewrite concat_length_eq. 2:eapply Forall2_impl_In; [|eauto]; intros; eapply Forall2_length; eauto.
              rewrite H22, <-length_clocksof_annots. congruence.
        }
        eapply ac_case in H23. rewrite <-H23.
        eapply IHe in H16; eauto.
        rewrite H7 in H16; simpl in H16. inv H16; eauto.
      }
    - (* app *)
      unfold clock_of_nclock, stripname.
      rewrite <-map_map.
      eapply sc_outside_mask' with (es0:=es); eauto.
      + rewrite Forall2_map_1. eapply Forall2_impl_In; [|eauto].
        intros (?&?&[|]) ??? Hv; simpl in *; auto.
        destruct Hv; auto.
      + eapply sc_exps'; eauto.
  Qed.

  Corollary sc_exps {prefs} : forall (G : @global prefs) H b env es ss,
      wc_global G ->
      sc_var_inv env H b ->
      Forall (wc_exp G env) es ->
      Forall2 (sem_exp_ck G H b) es ss ->
      Forall2 (sem_clock H b) (clocksof es) (map abstract_clock (concat ss)).
  Proof.
    intros * HwcG Hinv Hwc Hsem.
    eapply sc_exps'; eauto.
    eapply Forall_forall; intros.
    eapply sc_exp; eauto.
  Qed.

  Fact NoDupMembers_fresh_in_anon_in : forall vars e,
      NoDupMembers (vars ++ fresh_in e) ->
      NoDupMembers (vars ++ anon_in e).
  Proof.
    intros * Hndup.
    destruct e; auto; simpl in *.
    repeat rewrite app_assoc in *.
    apply NoDupMembers_app_l in Hndup; auto.
  Qed.

  (** ** Another version of semantics equivalence, including sem_clock_inputs *)
  Section sem_ref.
    Context {pref1 pref2 : PS.t}.

    (** We develop a notion of refinement over globals :
        [node_sem_refines G G' f] means that if [f] exists and has a given semantic in [G],
        then it also exists and has the same semantic in [G'].
        This is just a shorthand definition, but is useful when proving the correctness
        of transformation passes over the Lustre AST.
     *)
    Definition node_sem_refines (G : @global pref1) (G' : @global pref2) f : Prop :=
      forall ins outs, sem_node_ck G f ins outs -> sem_node_ck G' f ins outs.

    Definition global_sem_refines (G : @global pref1) (G' : @global pref2) : Prop :=
      forall f, node_sem_refines G G' f.

    Hint Resolve NoDupMembers_fresh_in_anon_in NoDupMembers_fresh_in' NoDupMembers_anon_in' nth_In.
    Hint Constructors sem_exp_ck.

    Fact sem_ref_sem_exp : forall G G' H b e vs,
        global_sem_refines G G' ->
        sem_exp_ck G H b e vs ->
        sem_exp_ck G' H b e vs.
    Proof with eauto.
      induction e using exp_ind2; intros * Href Hsem;
        inv Hsem...
      - (* fby *)
        econstructor...
        + repeat rewrite_Forall_forall...
        + repeat rewrite_Forall_forall...
      - (* arrow *)
        econstructor...
        + repeat rewrite_Forall_forall...
        + repeat rewrite_Forall_forall...
      - (* when *)
        econstructor...
        repeat rewrite_Forall_forall...
      - (* merge *)
        econstructor...
        do 2 (eapply Forall2_impl_In; [|eauto]; intros).
        do 2 (eapply Forall_forall in H0; eauto).
      - (* case *)
        econstructor...
        + clear H12. do 2 (eapply Forall2_impl_In; [|eauto]; intros; subst).
          do 2 (eapply Forall_forall in H0; eauto; simpl in H0).
        + eapply Forall2_impl_In; [|eauto]; intros.
          eapply Forall_forall in H1; eauto.
      - (* app *)
        econstructor...
        + repeat rewrite_Forall_forall...
        + repeat rewrite_Forall_forall...
        + intros k. specialize (H13 k).
          specialize (Href f (map (maskv k bs) (concat ss)) (map (maskv k bs) vs)).
          eapply Href; eauto.
    Qed.

    Fact sem_ref_sem_equation : forall G G' H b eq,
        global_sem_refines G G' ->
        sem_equation_ck G H b eq ->
        sem_equation_ck G' H b eq.
    Proof.
      intros G G' H b [xs es] Href Hsem.
      inv Hsem.
      econstructor; eauto.
      eapply Forall2_impl_In; [|eauto]; intros.
      eapply sem_ref_sem_exp; eauto.
    Qed.

    Fact global_sem_ref_nil : forall enums,
      global_sem_refines (Global enums []) (Global enums []).
    Proof.
      intros * f ins outs Hsem.
      inv Hsem. unfold find_node in H0; simpl in H0; inv H0.
    Qed.

    Fact global_sem_ref_cons : forall enums nds nds' n n' f,
        Ordered_nodes (Global enums (n::nds)) ->
        Ordered_nodes (Global enums (n'::nds')) ->
        n_name n = f ->
        n_name n' = f ->
        global_sem_refines (Global enums nds) (Global enums nds') ->
        node_sem_refines (Global enums (n::nds)) (Global enums (n'::nds')) f ->
        global_sem_refines (Global enums (n::nds)) (Global enums (n'::nds')).
    Proof with eauto.
      intros * Hord1 Hord2 Hname1 Hname2 Hglob Hnode f0 ins outs Hsem.
      destruct (ident_eq_dec (n_name n) f0); subst.
      + specialize (Hnode ins outs).
        eapply Hnode; eauto.
      + setoid_rewrite <-sem_node_ck_cons_iff...
        eapply Hglob.
        setoid_rewrite sem_node_ck_cons_iff...
    Qed.

  End sem_ref.

  (** ** Execution of a node with absent inputs *)

  Lemma sem_var_instant_absent: forall H x v,
      IStr.sem_var_instant H x v ->
      IStr.sem_var_instant (Env.map (fun _ => absent) H) x absent.
  Proof.
    intros * Var. unfold IStr.sem_var_instant in *.
    rewrite Env.Props.P.F.map_o, Var; auto.
  Qed.
  Hint Resolve sem_var_instant_absent.

  Lemma sem_clock_false: forall H ck b b',
      IStr.sem_clock b H ck b' ->
      IStr.sem_clock (fun _ => false) (fun n => Env.map (fun _ => absent) (H n)) ck (fun _ => false).
  Proof.
    intros * Sem n. specialize (Sem n).
    revert Sem. generalize (b n) (b' n). clear b b'.
    induction ck; intros * Sem; inv Sem; eauto using IStr.sem_clock_instant.
  Qed.

  Section sem_node_absent.
    Context {prefs : PS.t}.

    Import List.

    Lemma Forall2_sem_exp_absent: forall (f : list (Stream svalue) -> list (Stream svalue)) (G : @global prefs) H b es ss,
        Forall2 (fun e vs => sem_exp_ck G H b e (f vs)) es ss ->
        Forall2 (sem_exp_ck G H b) es (map f ss).
    Proof.
      intros * Sem. rewrite Forall2_map_2.
      eapply Forall2_impl_In; [|eauto]. auto.
    Qed.
    Hint Resolve Forall2_sem_exp_absent.

    Lemma sem_var_absent: forall H x v,
        sem_var H x v ->
        sem_var (Env.map (fun _ => Streams.const absent) H) x (Streams.const absent).
    Proof.
      intros * Var. inv Var.
      econstructor; eauto. 2:reflexivity.
      eapply PositiveMap.map_1 with (f:=fun _ => Streams.const absent); eauto.
    Qed.
    Hint Resolve sem_var_absent.

    Lemma sem_clock_absent: forall H bs ck bs',
        sem_clock H bs ck bs' ->
        sem_clock (Env.map (fun _ => Streams.const absent) H) (Streams.const false) ck (Streams.const false).
    Proof.
      intros * Hck.
      rewrite sem_clock_equiv in *.
      apply sem_clock_false in Hck.
      intros n. specialize (Hck n); simpl in *.
      setoid_rewrite Env.map_map. setoid_rewrite Env.map_map in Hck.
      now rewrite 2 tr_Stream_const.
    Qed.

    Lemma clocks_of_false: forall ss,
      clocks_of (map (fun _ : Stream svalue => Streams.const absent) ss) ≡ Streams.const false.
    Proof.
      intros *.
      eapply ntheq_eqst. intros n.
      rewrite clocks_of_nth, const_nth.
      induction ss; simpl; auto.
      rewrite const_nth; simpl; auto.
    Qed.

    Lemma sem_clock_inputs_false : forall (G : @global prefs) f xs,
        sem_clock_inputs G f xs ->
        sem_clock_inputs G f (map (fun _ => Streams.const absent) xs).
    Proof.
      intros * (H&n&Find&Sem&Ck).
      exists (Env.map (fun _ => Streams.const absent) H). exists n.
      repeat split; auto.
      - rewrite Forall2_map_2. eapply Forall2_impl_In; eauto using sem_var_absent.
      - rewrite map_map, Forall2_map_2 in *.
        eapply Forall2_impl_In; eauto. intros (?&?) ? _ _ SemCk.
        rewrite ac_Streams_const, clocks_of_false.
        rewrite sem_clock_equiv in *.
        clear - SemCk. eapply sem_clock_false in SemCk.
        intros n. specialize (SemCk n); simpl in *.
        rewrite tr_Stream_const.
        unfold CIStr.tr_history in *. rewrite Env.map_map in SemCk. rewrite Env.map_map.
        erewrite Env.map_ext; [eauto|].
        intros ?; simpl. rewrite tr_Stream_const. reflexivity.
    Qed.

    Lemma fby_absent:
      fby (Streams.const absent) (Streams.const absent) (Streams.const absent).
    Proof.
      cofix CoFix.
      rewrite CommonStreams.const_Cons. constructor; auto.
    Qed.

    Lemma arrow_absent:
      arrow (Streams.const absent) (Streams.const absent) (Streams.const absent).
    Proof.
      cofix CoFix.
      rewrite CommonStreams.const_Cons. constructor; auto.
    Qed.

    Fact clocked_app_absent: forall H bs vars xs,
        clocked_app H bs vars xs ->
        clocked_app (Env.map (fun _ => Streams.const absent) H) (Streams.const false) vars (map (fun _ => Streams.const absent) xs).
    Proof.
      unfold clocked_app.
      intros * Hckapp.
      rewrite Forall2_map_2.
      eapply Forall2_impl_In; [|eauto]; intros (?&?&[|]) ? _ _ ?; simpl in *; auto.
      destruct H0 as (Hvar&Hck).
      split; eauto.
      eapply sem_clock_absent in Hck. now rewrite ac_Streams_const.
    Qed.

    Fact clocked_node_absent: forall H bs vars bcks,
        clocked_node H bs vars bcks ->
        clocked_node (Env.map (fun _ => Streams.const absent) H) (Streams.const false) vars bcks.
    Proof.
      unfold clocked_node.
      intros * (Hdom&Hsc).
      split.
      - now rewrite Env.dom_map.
      - eapply Forall_impl; [|eauto]; intros (?&?) (?&Hvar&Hck).
        exists (Streams.const absent). split; eauto.
        eapply sem_clock_absent in Hck. now rewrite ac_Streams_const.
    Qed.

    Lemma sem_block_absent:
      forall (G : @global prefs) H bs bck,
        sem_block_ck G H bs bck ->
        sem_block_ck G (Env.map (fun _ => Streams.const absent) H) (Streams.const false) bck.
    Proof.
      intros * Sem.
      eapply sem_block_ck_ind2
        with (P_exp := fun H _ e vs => sem_exp_ck G (Env.map (fun _ => Streams.const absent) H)
                                                (Streams.const false) e (List.map (fun _ => Streams.const absent) vs))
             (P_equation := fun H _ eq => sem_equation_ck G (Env.map (fun _ => Streams.const absent) H) (Streams.const false) eq)
             (P_block := fun H _ bck => sem_block_ck G (Env.map (fun _ => Streams.const absent) H) (Streams.const false) bck)
             (P_node := fun f xs ys => sem_node_ck G f (map (fun _ => Streams.const absent) xs) (map (fun _ => Streams.const absent) ys));
        simpl in *; subst; intros; eauto.
      - (* Econst *)
        simpl. constructor.
        apply ntheq_eqst. intros n.
        rewrite const_nth. symmetry.
        apply const_false, const_nth.
      - (* Eenum *)
        simpl. constructor.
        apply ntheq_eqst. intros n.
        rewrite const_nth. symmetry.
        apply enum_false, const_nth.
      - (* Evar *)
        econstructor; eauto.
      - (* Eunop *)
        econstructor; eauto.
        eapply lift1_spec; intros.
        left. split; apply const_nth.
      - (* Ebinop *)
        econstructor; eauto.
        eapply lift2_spec; intros.
        left. repeat split; apply const_nth.
      - (* Efby *)
        econstructor.
        1,2:erewrite Forall2_map_2; eapply Forall2_impl_In; [|eauto]; intros ???? Hsem; eapply Hsem; eauto.
        repeat rewrite <-concat_map. rewrite Forall3_map_1, Forall3_map_2, Forall3_map_3.
        eapply Forall3_impl_In; [|eauto]. intros * _ _ _ _. apply fby_absent.
      - (* Earrow *)
        econstructor.
        1,2:erewrite Forall2_map_2; eapply Forall2_impl_In; [|eauto]; intros ???? Hsem; eapply Hsem; eauto.
        repeat rewrite <-concat_map. rewrite Forall3_map_1, Forall3_map_2, Forall3_map_3.
        eapply Forall3_impl_In; [|eauto]. intros * _ _ _ _. apply arrow_absent.
      - (* Ewhen *)
        econstructor; eauto.
        rewrite <-concat_map, Forall2_map_1, Forall2_map_2.
        eapply Forall2_impl_In; [|eauto]. intros ?? _ _ When.
        apply when_spec. intros n.
        left. repeat split; apply const_nth.
      - (* Emerge *)
        econstructor; eauto.
        + clear H2.
          do 2 (erewrite Forall2_map_2; eapply Forall2_impl_In; [|eauto]; intros); eauto.
          eapply H9; eauto.
        + replace (map (@concat _) (map (fun b0 => map (map (fun _ => Streams.const absent)) b0) vs))
            with (map (map (fun _ => Streams.const absent)) (map (@concat _) vs)).
          2:{ rewrite map_map, map_map.
              eapply map_ext; intros. apply concat_map. }
          rewrite Forall2Transpose_map_1, Forall2Transpose_map_2.
          eapply Forall2Transpose_impl; [|eauto]; intros.
          eapply merge_spec. intros n. left.
          repeat split.
          2: rewrite Forall_map; apply Forall_forall; intros.
          1-3:apply const_nth.
      - (* Ecase *)
        econstructor. eauto.
        + clear H5.
          do 2 (erewrite Forall2_map_2; eapply Forall2_impl_In; [|eauto]; intros; subst); eauto.
          eapply H13; eauto.
        + clear H3 H4. rewrite Forall2_map_2.
          eapply Forall2_impl_In; [|eauto]; intros; simpl in *.
          erewrite Forall2_map_1, Forall2_map_2. eapply Forall2_impl_In; [|eauto]; intros.
          eapply map_st_EqSt with (y:=fun _ => Streams.const absent); eauto.
          intros; reflexivity.
        + erewrite Forall2_map_2.
          eapply Forall2_impl_In; [|eauto]; intros. eapply H11; eauto.
        + replace (map (@concat _) (map (fun b0 => map (map (fun _ => Streams.const absent)) b0) vs))
            with (map (map (fun _ => Streams.const absent)) (map (@concat _) vs)).
          2:{ rewrite map_map, map_map.
              eapply map_ext; intros. apply concat_map. }
          rewrite Forall2Transpose_map_1, Forall2Transpose_map_2.
          eapply Forall2Transpose_impl; [|eauto]; intros.
          eapply case_spec. intros n. left.
          repeat split.
          2: rewrite Forall_map; apply Forall_forall; intros.
          1-3:apply const_nth.
      - (* Eapp *)
        econstructor.
        1,2:erewrite Forall2_map_2; eapply Forall2_impl_In; [|eauto]; intros ???? Hsem; eapply Hsem; eauto.
        eauto using bools_ofs_absent.
        + intros k. specialize (H6 k) as (?&SemN).
          repeat rewrite map_map in *.
          eapply sem_node_ck_morph; try eapply SemN; eauto.
          rewrite <-concat_map, map_map.
          1,2:eapply map_st_EqSt_Proper; try reflexivity.
          1,2:intros * Eq; symmetry; apply mask_absent.
        + eapply clocked_app_absent; eauto.
      - (* Equation *)
        econstructor; eauto.
        rewrite <-concat_map, Forall2_map_2.
        eapply Forall2_impl_In; eauto.
      - (* Beq *)
        econstructor; eauto.
      - (* Breset *)
        econstructor. eapply H2; eauto.
        apply bools_of_absent.
        intros k. specialize (H4 k) as (_&Hsem').
        eapply Forall_impl; [|eauto]; intros; simpl in *.
        rewrite maskb_absent.
        eapply sem_block_refines; [|eauto].
        rewrite mask_hist_absent, mask_hist_absent'. reflexivity.
      - (* Node *)
        econstructor. 5:reflexivity. 1-4:eauto; subst.
        1,2:(rewrite Forall2_map_2; eapply Forall2_impl_In; [|eauto];
             intros; eapply sem_var_absent; eauto).
        + eapply Forall_impl; [|eapply H5]; intros.
          rewrite clocks_of_false; auto.
        + rewrite clocks_of_false.
          eapply clocked_node_absent; eauto.
    Qed.

  End sem_node_absent.

End LCLOCKSEMANTICS.

Module LClockSemanticsFun
       (Ids : IDS)
       (Op : OPERATORS)
       (OpAux : OPERATORS_AUX Ids Op)
       (Cks : CLOCKS Ids Op OpAux)
       (Syn : LSYNTAX Ids Op OpAux Cks)
       (Clo : LCLOCKING Ids Op OpAux Cks Syn)
       (LCA : LCAUSALITY Ids Op OpAux Cks Syn)
       (Lord : LORDERED Ids Op OpAux Cks Syn)
       (CStr : COINDSTREAMS Ids Op OpAux Cks)
       (Sem : LSEMANTICS Ids Op OpAux Cks Syn Lord CStr)
<: LCLOCKSEMANTICS Ids Op OpAux Cks Syn Clo LCA Lord CStr Sem.
  Include LCLOCKSEMANTICS Ids Op OpAux Cks Syn Clo LCA Lord CStr Sem.
End LClockSemanticsFun.
