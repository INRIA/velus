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
       (Import LCA          : LCAUSALITY Ids Op OpAux Cks Syn)
       (Import Lord  : LORDERED Ids Op OpAux Cks Syn)
       (Import CStr  : COINDSTREAMS Ids Op OpAux Cks)
       (Import Sem   : LSEMANTICS Ids Op OpAux Cks Syn Lord CStr).

  Import CStr.
  Module IStr := IndexedStreamsFun Ids Op OpAux Cks.
  Module Import CIStr := CoindIndexedFun Ids Op OpAux Cks CStr IStr.

  Module Import Det := LSemDeterminismFun Ids Op OpAux Cks Syn LCA Lord CStr Sem.

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

  Lemma sem_clock_refines' : forall vars H H' ck bs bs',
      wc_clock vars ck ->
      (forall x vs, InMembers x vars -> sem_var H x vs -> sem_var H' x vs) ->
      sem_clock H bs ck bs' ->
      sem_clock H' bs ck bs'.
  Proof.
    intros * Hwc Href Hsem.
    rewrite sem_clock_equiv in *. intros n. specialize (Hsem n).
    assert (forall x v, InMembers x vars ->
                   IStr.sem_var_instant (CIStr.tr_history H n) x v ->
                   IStr.sem_var_instant (CIStr.tr_history H' n) x v) as Href'.
    { intros * Hinm Hvar. unfold IStr.sem_var_instant, CIStr.tr_history in *.
      rewrite Env.Props.P.F.map_o in *.
      eapply option_map_inv in Hvar as (?&Hfind&?); subst.
      eapply Href in Hinm. 2:econstructor; eauto; reflexivity.
      inv Hinm. rewrite H1; simpl. f_equal. now rewrite H2.
    } clear Href.
    revert bs bs' Hwc Hsem.
    induction ck; intros * Hwc Hsem; inv Hwc.
    - inv Hsem; constructor; auto.
    - inv Hsem.
      + econstructor; eauto.
        * rewrite H6. eapply IHck; eauto. rewrite <-H6; auto.
        * eapply Href'; eauto using In_InMembers.
      + econstructor; eauto.
        * rewrite H6. eapply IHck; eauto. rewrite <-H6; auto.
        * eapply Href'; eauto using In_InMembers.
      + eapply IStr.Son_abs2; eauto.
        * specialize (IHck bs (Streams.const true)).
          rewrite tr_Stream_const in IHck; auto.
        * eapply Href'; eauto using In_InMembers.
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

  (** * Alignment proof *)

  Local Ltac simpl_ndup Hnd :=
    simpl in *;
    try rewrite app_nil_r in Hnd; repeat rewrite map_app.
  Local Ltac ndup_l H := rewrite app_assoc in H; apply NoDup_app_l in H; auto.
  Local Ltac ndup_r H := rewrite Permutation_swap in H; apply NoDup_app_r in H; auto.

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

    Context {PSyn : block -> Prop}.
    Context {prefs : PS.t}.
    Variable (G: @global PSyn prefs).

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

    Hint Resolve Env.union_refines2 Env.union_dom' Env.adds_opt'_refines Env.adds_opt'_dom
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
            Env.dom H env ->
            NoDup (env ++ map fst (fresh_in e)) ->
            wl_exp G e ->
            Sem.sem_exp G H b e vs ->
            exists H',
              Env.refines (@EqSt _) H H' /\ Env.dom H' (env ++ map fst (fresh_in e)) /\
              anon_sem_exp H' b e) es ->
      Env.dom H env ->
      NoDup (env ++ map fst (flat_map fresh_in es)) ->
      Forall (wl_exp G) es ->
      Forall2 (Sem.sem_exp G H b) es vs ->
      exists H', Env.refines (@EqSt _) H H' /\
            Env.dom H' (env ++ map fst (flat_map fresh_in es)) /\
            Forall (anon_sem_exp H' b) es.
    Proof.
      induction es; intros * Hf Hdom Hnd Hwl Hsem;
        inv Hwl; inv Hsem; inv Hf.
      - simpl_ndup Hnd. exists H; auto.
      - simpl_ndup Hnd.
        eapply IHes in H7 as (H'2&Hr2&Hd2&Hs2); eauto. 2:solve_NoDup_app. clear IHes.
        eapply H5 in H4 as (H'1&Hr1&Hd1&Hs1); eauto. 2:solve_NoDup_app. clear H5.
        exists (Env.union H'1 H'2). repeat split; auto.
        apply NoDup_app_r in Hnd. rewrite map_app in Hnd.
        constructor; eauto. 2:eapply Forall_impl; [|eauto]; intros.
        1,2:eapply anon_sem_exp_refines. 2,4:eauto.
        eapply Env.union_refines3 in Hdom; eauto.
        eapply Env.union_refines4 in Hdom; eauto.
    Qed.

    Corollary sem_exps_fresh2 : forall env H b es vs,
        Forall
          (Forall
            (fun e => forall vs,
                  Env.dom H env ->
                  NoDup (env ++ map fst (fresh_in e)) ->
                  wl_exp G e ->
                  Sem.sem_exp G H b e vs ->
                  exists H',
                    Env.refines (@EqSt _) H H' /\ Env.dom H' (env ++ map fst (fresh_in e)) /\
                    anon_sem_exp H' b e)) es ->
        Env.dom H env ->
        NoDup (env ++ map fst (flat_map (flat_map fresh_in) es)) ->
        Forall (Forall (wl_exp G)) es ->
        Forall2 (Forall2 (Sem.sem_exp G H b)) es vs ->
        exists H',
          Env.refines (@EqSt _) H H' /\
          Env.dom H' (env ++ map fst (flat_map (flat_map fresh_in) es)) /\
          Forall (Forall (anon_sem_exp H' b)) es.
    Proof.
      induction es; intros * Hf Hdom Hnd Hwl Hsem;
        inv Hwl; inv Hsem; inv Hf.
      - simpl_ndup Hnd. exists H; auto.
      - simpl_ndup Hnd.
        eapply IHes in H7 as (H'2&Hr2&Hd2&Hs2); eauto. 2:solve_NoDup_app. clear IHes.
        eapply sem_exps_fresh1 in H5 as (H'1&Hr1&Hd1&Hs1); eauto. 2:solve_NoDup_app.
        exists (Env.union H'1 H'2). repeat split; auto.
        apply NoDup_app_r in Hnd. rewrite map_app in Hnd.
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
                    Env.dom H env ->
                    NoDup (env ++ map fst (fresh_in e)) ->
                    wl_exp G e ->
                    Sem.sem_exp G H b e vs ->
                    exists H',
                      Env.refines (@EqSt _) H H' /\
                      Env.dom H' (env ++ map fst (fresh_in e)) /\
                      anon_sem_exp H' b e))) brs ->
        NoDup (env ++ map fst (flat_map (or_default_with [] (flat_map fresh_in)) brs)) ->
        Env.dom H env ->
        (forall es, In (Some es) brs -> Forall (wl_exp G) es) ->
        Forall2 (fun oes vs => forall es, oes = Some es -> Forall2 (Sem.sem_exp G H b) es vs) brs vs ->
        exists H',
          Env.refines (@EqSt _) H H' /\
          Env.dom H' (env ++ map fst (flat_map (or_default_with [] (flat_map fresh_in)) brs)) /\
          Forall (fun oes => forall es, oes = Some es -> Forall (anon_sem_exp H' b) es) brs.
    Proof.
      induction brs; intros * Hf Hnd Hdom Hwl Hsem; inv Hsem; inv Hf.
      - simpl_ndup Hnd. exists H. auto.
      - simpl_ndup Hnd.
        eapply IHbrs in H5 as (H'2&Hr2&Hd2&Hs2); eauto. 2:solve_NoDup_app. clear IHbrs.
        destruct a; simpl in *.
        + eapply sem_exps_fresh1 in H3 as (H'1&Hr1&Hd1&Hs1); eauto. 2:solve_NoDup_app.
          exists (Env.union H'1 H'2). repeat split; auto.
          apply NoDup_app_r in Hnd. rewrite map_app in Hnd.
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
        Env.dom H env ->
        NoDup (env ++ map fst (fresh_in e)) ->
        wl_exp G e ->
        Sem.sem_exp G H b e vs ->
        exists H', Env.refines (@EqSt _) H H' /\
              Env.dom H' (env ++ map fst (fresh_in e)) /\
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
        eapply IHe1 in H9 as (H'1&Href1&Hdom1&?); eauto. 2:solve_NoDup_app.
        eapply IHe2 in H12 as (H'2&Href2&Hdom2&?); eauto. 2:solve_NoDup_app.
        exists (Env.union H'1 H'2). repeat split; auto.
        apply NoDup_app_r in Hnd. rewrite map_app in Hnd.
        econstructor; eauto.
        1,2:eapply anon_sem_exp_refines; [|eauto].
        eapply Env.union_refines3 in Hdom; eauto.
        eapply Env.union_refines4 in Hdom; eauto.
      - (* fby *)
        eapply sem_exps_fresh1 in H0 as (H'0&Hr0&Hd0&Hs0); eauto. 2:solve_NoDup_app.
        eapply sem_exps_fresh1 in H1 as (H'1&Hr1&Hd1&Hs1); eauto. 2:solve_NoDup_app.
        exists (Env.union H'0 H'1). repeat split; auto 10.
        apply NoDup_app_r in Hnd. repeat rewrite map_app in Hnd.
        econstructor; eauto.
        1-2:eapply Forall_impl; [|eauto]; simpl; intros; eapply anon_sem_exp_refines; [|eauto].
        eapply Env.union_refines3 with (m:=H). 1-8:eauto.
        eapply Env.union_refines4 with (m:=H). 1-8:eauto.
      - (* arrow *)
        eapply sem_exps_fresh1 in H0 as (H'0&Hr0&Hd0&Hs0); eauto. 2:solve_NoDup_app.
        eapply sem_exps_fresh1 in H1 as (H'1&Hr1&Hd1&Hs1); eauto. 2:solve_NoDup_app.
        exists (Env.union H'0 H'1). repeat split; auto 10.
        apply NoDup_app_r in Hnd. repeat rewrite map_app in Hnd.
        econstructor; eauto.
        1-2:eapply Forall_impl; [|eauto]; simpl; intros; eapply anon_sem_exp_refines; [|eauto].
        eapply Env.union_refines3 with (m:=H). 1-8:eauto.
        eapply Env.union_refines4 with (m:=H). 1-8:eauto.
      - (* when *)
        eapply sem_exps_fresh1 in H0 as (H'1&Hr1&Hd1&Hs1); eauto.
      - (* merge *)
        eapply sem_exps_fresh2 in H0 as (H'1&Hr1&Hd1&Hs1); eauto.
      - (* case *)
        eapply IHe in H14 as (H'0&Hr0&Hd0&Hsd0); eauto. 2:solve_NoDup_app.
        eapply sem_exps_fresh3 in H0 as (H'1&Hr1&Hd1&Hs1); eauto. 2:solve_NoDup_app.
        eapply sem_exps_fresh1 in H20 as (H'2&Hr2&Hd2&Hsd2); eauto. 2:solve_NoDup_app.
        exists (Env.union H'0 (Env.union H'1 H'2)); repeat split; auto.
        econstructor; eauto.
        2:clear H17 H19; do 2 (eapply Forall_impl; [|eauto]; intros; subst).
        3:eapply Forall_impl; [|eauto]; intros; subst.
        1-3:eapply anon_sem_exp_refines; [|eauto].
        eapply Env.union_refines3 with (m:=H) (xs:=env0) (ys:=map fst (fresh_in e)); eauto. solve_NoDup_app.
        1,2:etransitivity; [|eapply Env.union_refines4'; eauto].
        eapply Env.union_refines3 with (m:=H). 3-5:eauto. 1-4:eauto. solve_NoDup_app.
        eapply Env.union_refines4'; eauto.
      - (* app *)
        eapply sem_exps_fresh1 in H0 as (H'0&Hr0&Hd0&Hs0); eauto. 2:solve_NoDup_app.
        eapply sem_exps_fresh1 in H1 as (H'1&Hr1&Hd1&Hs1); eauto. 2:solve_NoDup_app.
        2:eapply Forall2_map_2; eapply H17.
        assert (length vs = length a) as Hlen.
        { specialize (H19 0). inv H19. rewrite H1 in H10; inv H10.
          apply Forall2_length in H3. unfold idents in H3. repeat rewrite map_length in H3.
          congruence. }
        remember (Env.adds_opt' (anons a) vs (Env.union H'0 H'1)) as H'3.
        repeat rewrite map_app in Hnd.
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
        Env.dom H env ->
        NoDup (env ++ map fst (anon_in e)) ->
        Forall2 (fun '(_, (_, o)) s => LiftO True (fun x : ident => sem_var H x s) o) (annot e) vs ->
        wl_exp G e ->
        Sem.sem_exp G H b e vs ->
        exists H', Env.refines (@EqSt _) H H' /\
          Env.dom H' (env ++ map fst (anon_in e)) /\
          anon_sem_exp H' b e.
    Proof.
      intros * Hdom Hndup Hf Hwl Hsem.
      destruct e; simpl in *.
      1-10:eapply sem_exp_fresh in Hsem as (H'&?&?&?); simpl in *; eauto.
      (* app *)
      inv Hwl; inv Hsem.
      unfold fresh_ins in *.
      assert (Hsem0:=H13). eapply sem_exps_fresh1 in H13 as (H'1&Hr1&?&?); eauto. 3:solve_NoDup_app.
      2:{ eapply Forall_forall; intros * Hin ?????.
          eapply sem_exp_fresh; eauto. }
      assert (Hsem1:=H15). eapply Forall2_map_2 in H15.
      eapply sem_exps_fresh1 in H15 as (H'2&Hr2&?&?); eauto. 3:solve_NoDup_app.
      2:{ eapply Forall_forall; intros * Hin ?????.
          eapply sem_exp_fresh; eauto. }
      assert (Env.dom (Env.union H'1 H'2) (env0 ++ map fst (fresh_ins l) ++ map fst (fresh_ins l0))) as Hd3 by eauto.
      exists (Env.union H'1 H'2). repeat split; auto.
      - repeat rewrite map_app. eauto.
      - rewrite map_app in Hndup.
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
        Env.dom H env ->
        NoDup (env ++ map fst (anon_ins es)) ->
        Forall2 (fun '(_, (_, o)) s => LiftO True (fun x : ident => sem_var H x s) o) (annots es) (concat vs) ->
        Forall (wl_exp G) es ->
        Forall2 (Sem.sem_exp G H b) es vs ->
        exists H', Env.refines (@EqSt _) H H' /\
          Env.dom H' (env ++ map fst (anon_ins es)) /\
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
        eapply IHHsem in Hvar2 as (H'2&?&?&?); eauto. 2:solve_NoDup_app. clear IHHsem.
        eapply sem_exp_anon in H0 as (H'1&?&?&?); eauto. 2:solve_NoDup_app.
        exists (Env.union H'1 H'2). repeat split; auto.
        + rewrite map_app; auto.
        + apply NoDup_app_r in Hnd. rewrite map_app in Hnd.
          constructor; auto.
          2:eapply Forall_impl; [|eauto]; intros.
          1,2:eapply anon_sem_exp_refines; [|eauto].
          eapply Env.union_refines3 in Hdom; eauto.
          eapply Env.union_refines4 in Hdom; eauto.
    Qed.

    Lemma sem_equation_anon : forall env H b equ,
        Env.dom H (map fst env) ->
        NoDupMembers (env ++ idck (anon_in_eq equ)) ->
        wc_equation G env equ ->
        Sem.sem_equation G H b equ ->
        exists H', Env.refines (@EqSt _) H H' /\
          Env.dom H' (map fst env ++ map fst (anon_in_eq equ)) /\
          anon_sem_equation H' b equ.
    Proof.
      intros ? ? ? (xs&es) Hdom Hnd Hwc Hsem.
      destruct Hwc as (Hwc1&Hwc2&_). inv Hsem.
      eapply sem_exps_anon in H5 as (H'&?&?&?); eauto.
      - now rewrite fst_NoDupMembers, map_app, map_fst_idck in Hnd.
      - clear - Hwc2 H6.
        rewrite Forall2_swap_args, nclocksof_annots, Forall2_map_1 in Hwc2.
        eapply Forall2_trans_ex in H6; [|eauto]. clear - H6.
        eapply Forall2_impl_In; eauto. intros (?&?&?) ??? (?&?&?&?).
        destruct o; simpl in *; subst; auto.
    Qed.

    (** Properties of sem_exp_anon *)

    Lemma idck_idty_inv : forall xs,
        exists xs' : list (ident * (type * clock * ident)), xs = idck (idty xs').
    Proof.
      induction xs as [|(x&ck)]; intros *.
      - exists []; auto.
      - destruct IHxs as (xs'&Heq); subst.
        exists ((x, (bool_velus_type, ck, xH))::xs'); auto.
    Qed.

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
        { pose proof (idck_idty_inv env0) as (?&?); subst.
          eapply det_exps in H13; eauto.
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
            eapply EqStN_EqSts, det_nodes_ins; eauto.
          - eapply Forall_wc_exp_wx_exp in H1; eauto. rewrite map_fst_idck, map_fst_idty in H1.
            erewrite map_fst_idcaus; eauto.
          - eapply Forall_wc_exp_wx_exp in H0; eauto. rewrite map_fst_idck, map_fst_idty in H0.
            erewrite map_fst_idcaus; eauto. }
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
    Definition sc_vars env H bs :=
      Forall (fun '(x, ck) => exists xs, sem_var H x xs /\ sem_clock H bs ck (abstract_clock xs)) env.

    Definition clocked_node H bs (env : list (ident * (type * clock))) blk :=
      Env.dom H (map fst (env ++ local_anon_in_block blk)) /\
      sc_vars (idck env) H bs.

    Definition clocked_app H bs (lann: list (type * nclock)) vss :=
      Forall2 (fun '(_, (ck, o)) vs =>
                 LiftO True (fun x => sem_var H x vs /\ sem_clock H bs ck (abstract_clock vs)) o) lann vss.

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

    Context {PSyn : block -> Prop}.
    Context {prefs : PS.t}.
    Variable G : @global PSyn prefs.

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

    with sem_block_ck : history -> Stream bool -> block -> Prop :=
    | Sbeq:
        forall H b eq,
          sem_equation_ck H b eq ->
          sem_block_ck H b (Beq eq)
    | Sreset:
        forall H b blks er sr r,
          sem_exp_ck H b er [sr] ->
          bools_of sr r ->
          (forall k, Forall (sem_block_ck (mask_hist k r H) (maskb k r b)) blks) ->
          sem_block_ck H b (Breset blks er)
    | Slocal:
        forall H H' b locs blks,
          (forall x vs, sem_var H' x vs -> ~InMembers x locs -> ~InMembers x (flat_map local_anon_in_block blks) -> sem_var H x vs) ->
          Env.dom H' (map fst (Env.elements H) ++ map fst locs ++ map fst (flat_map local_anon_in_block blks)) ->
          sc_vars (idck (idty locs)) H' b ->
          Forall (sem_block_ck H' b) blks ->
          sem_block_ck H b (Blocal locs blks)

    with sem_node_ck: ident -> list (Stream svalue) -> list (Stream svalue) -> Prop :=
      Snode:
        forall f ss os n H b,
          find_node f G = Some n ->
          Forall2 (sem_var H) (idents n.(n_in)) ss ->
          Forall2 (sem_var H) (idents n.(n_out)) os ->
          sem_block_ck H b n.(n_block) ->
          b = clocks_of ss ->
          clocked_node H b (idty (n.(n_in) ++ n.(n_out))) n.(n_block) ->
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

      Hypothesis BlocalCase:
        forall H H' b locs blks,
          (forall x vs, sem_var H' x vs -> ~(InMembers x locs) -> ~(InMembers x (flat_map local_anon_in_block blks)) -> sem_var H x vs) ->
          Env.dom H' (map fst (Env.elements H) ++ map fst locs ++ map fst (flat_map local_anon_in_block blks)) ->
          sc_vars (idck (idty locs)) H' b ->
          Forall (sem_block_ck H' b) blks ->
          Forall (P_block H' b) blks ->
          P_block H b (Blocal locs blks).

      Hypothesis Node:
        forall f ss os n H b,
          find_node f G = Some n ->
          Forall2 (sem_var H) (idents n.(n_in)) ss ->
          Forall2 (sem_var H) (idents n.(n_out)) os ->
          sem_block_ck H b n.(n_block) ->
          P_block H b n.(n_block) ->
          b = clocks_of ss ->
          clocked_node H b (idty (n.(n_in) ++ n.(n_out))) n.(n_block) ->
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
          + eapply BlocalCase; eauto. clear H1 H2. SolveForall.
        - inv Sem.
          eapply Node; eauto.
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

      Fact sc_vars_refines : forall env H H' b,
          Env.refines (@EqSt _) H H' ->
          sc_vars env H b ->
          sc_vars env H' b.
      Proof.
        intros * Href Hsc.
        unfold sc_vars in *.
        eapply Forall_impl; [|eauto].
        intros (?&?) (?&Hvar&Hck).
        exists x. split.
        - eapply sem_var_refines; eauto.
        - eapply sem_clock_refines; eauto.
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
        - (* local *)
          assert (Env.refines (@EqSt _) H'0
                              (Env.restrict (Env.union H' H'0) (map fst (Env.elements H') ++ map fst locs ++ map fst (flat_map local_anon_in_block blocks)))).
          { intros ?? Hfind. exists v. split; try reflexivity.
            apply Env.restrict_find; eauto using Env.union_find3'.
            eapply incl_appl'. eapply Env.refines_elements; eauto.
            eapply Env.dom_use; eauto. esplit; eauto. }
          eapply Slocal with (H':=Env.restrict  (Env.union H' H'0) (map fst (Env.elements H') ++ map fst locs ++ map fst (flat_map local_anon_in_block blocks))); eauto.
          + intros * Hvar Hnin1 Hnin2.
            eapply sem_var_restrict_inv in Hvar as (_&Hvar). inv Hvar.
            eapply Env.union_find4' in H3 as [(Hfind1&Hfind2)|Hfind2].
            * econstructor; eauto.
            * eapply sem_var_refines; eauto. eapply H4; eauto. econstructor; eauto.
          + eapply Env.dom_lb_restrict_dom, Env.union_dom_lb; eauto.
            * eapply Env.dom_dom_lb, Env.dom_elements.
            * eapply Env.dom_lb_incl, Env.dom_dom_lb; eauto. solve_incl_app.
          + eapply sc_vars_refines; eauto.
          + rewrite Forall_forall in *; intros. eapply H; eauto.
      Qed.

    End sem_refines.

    Section sem_restrict.

      Lemma sem_clock_restrict : forall vars ck H bs bs',
        wc_clock vars ck ->
        sem_clock H bs ck bs' ->
        sem_clock (Env.restrict H (map fst vars)) bs ck bs'.
      Proof.
        intros * Hwc Hsem.
        eapply sem_clock_refines'; [eauto| |eauto].
        intros ?? Hinm Hvar.
        eapply sem_var_restrict; eauto. apply fst_InMembers; auto.
      Qed.

      Corollary clocked_app_restrict : forall (vars anons : list (ident * clock)) H bs ncks vs,
          (forall x, InMembers x (anon_streams (map snd ncks)) -> InMembers x (vars ++ anons)) ->
          Forall (wc_clock (vars ++ anons)) (map clock_of_nclock ncks) ->
          clocked_app H bs ncks vs ->
          clocked_app (Env.restrict H (map fst (vars++anons))) bs ncks vs.
      Proof.
        intros * Hincl Hwc Hclocked.
        eapply Forall2_impl_In; [|eauto]; intros (?&(?&[|])) ? Hin1 Hin2 Hv; simpl in *; auto.
        destruct Hv as (Hv&Hck).
        split; auto.
        - eapply sem_var_restrict; eauto.
          eapply fst_InMembers, Hincl, fst_InMembers.
          eapply in_map_iff. exists (i, c); split; auto.
          eapply map_filter_In. eapply in_map_iff; do 2 esplit; eauto; auto.
          reflexivity.
        - eapply sem_clock_restrict; eauto.
          eapply Forall_forall in Hwc; eauto.
          eapply in_map_iff. do 2 esplit; eauto; auto.
      Qed.

      Hypothesis HwcG : wc_global G.

      Lemma sem_exp_restrict : forall vars anons H b e vs,
          wc_env vars ->
          incl (fresh_in e) anons ->
          wc_exp G vars e ->
          sem_exp_ck H b e vs ->
          sem_exp_ck (Env.restrict H (List.map fst vars ++ List.map fst anons)) b e vs.
      Proof with eauto.
        induction e using exp_ind2; intros vs Hwenv Hincl Hwc Hsem;
          inv Hwc; inv Hsem; simpl in *.
        - (* const *) constructor...
        - (* enum *) constructor...
        - (* var *)
          constructor. eapply sem_var_restrict...
          eapply in_app, or_introl, in_map_iff; do 2 esplit; eauto. reflexivity.
        - (* var (anon) *)
          constructor. eapply sem_var_restrict...
          eapply in_app, or_introl, in_map_iff; do 2 esplit; eauto. reflexivity.
        - (* unop *)
          econstructor...
        - (* binop *)
          eapply incl_app' in Hincl as (?&?).
          econstructor...
        - (* fby *)
          eapply incl_app' in Hincl as (Hincl1&Hincl2).
          econstructor... 1,2:rewrite Forall_forall in *.
          + eapply Forall2_impl_In; [|eauto]; intros. eapply H0...
            etransitivity; [|apply Hincl1]. intros ??; eapply in_flat_map...
          + eapply Forall2_impl_In; [|eauto]; intros. eapply H1...
            etransitivity; [|apply Hincl2]. intros ??; eapply in_flat_map...
        - (* arrow *)
          eapply incl_app' in Hincl as (Hincl1&Hincl2).
          econstructor... 1,2:rewrite Forall_forall in *.
          + eapply Forall2_impl_In; [|eauto]; intros. eapply H0...
            etransitivity; [|apply Hincl1]. intros ??; eapply in_flat_map...
          + eapply Forall2_impl_In; [|eauto]; intros. eapply H1...
            etransitivity; [|apply Hincl2]. intros ??; eapply in_flat_map...
        - (* when *)
          econstructor... rewrite Forall_forall in *.
          + eapply Forall2_impl_In; [|eauto]; intros. eapply H0...
            etransitivity; [|apply Hincl]. intros ??; eapply in_flat_map...
          + eapply sem_var_restrict...
            eapply in_app, or_introl, in_map_iff; do 2 esplit... reflexivity.
        - (* merge *)
          econstructor...
          + eapply sem_var_restrict...
            eapply in_app, or_introl, in_map_iff; do 2 esplit... reflexivity.
          + do 2 (eapply Forall2_impl_In; [|eauto]; intros).
            do 2 (eapply Forall_forall in H6; eauto).
            do 2 (eapply Forall_forall in H0; eauto).
            eapply H0...
            etransitivity; [|eapply Hincl].
            intros ??; eapply in_flat_map... do 2 esplit... eapply in_flat_map...
        - (* case *)
          eapply incl_app' in Hincl as (Hincl1&Hincl2). eapply incl_app' in Hincl2 as (Hincl2&Hincl3).
          econstructor... 1-3:rewrite Forall_forall in *.
          + clear H21. do 2 (eapply Forall2_impl_In; [|eauto]; intros; subst).
            specialize (H0 _ H2); simpl in *.
            eapply Forall_forall in H0; eauto; simpl in *. eapply H0...
            2:eapply Forall_forall in H9; eauto.
            etransitivity; [|eapply Hincl2].
            intros ??; eapply in_flat_map... do 2 esplit... eapply in_flat_map...
          + eapply Forall2_impl_In; [|eauto]; intros; subst.
            eapply H1... etransitivity; [|eauto]. intros ??; eapply in_flat_map...
        - (* app *)
          apply incl_app' in Hincl as (Hincl1&Hincl2). apply incl_app' in Hincl2 as (Hincl2&Hincl3).
          econstructor...
          + eapply Forall2_impl_In; [|eauto]; intros. rewrite Forall_forall in *...
            eapply H0... etransitivity; [|eapply Hincl1].
            intros ??. eapply in_flat_map...
          + eapply Forall2_impl_In; [|eauto]; intros. rewrite Forall_forall in *...
            eapply H1... etransitivity; [|eapply Hincl2].
            intros ??. eapply in_flat_map...
          + rewrite <-map_fst_idck, <-map_app. eapply clocked_app_restrict; eauto.
            * intros ? Hin. rewrite InMembers_app, InMembers_idck. right. eapply InMembers_incl; eauto.
              now rewrite <-InMembers_idck, <-anon_streams_anon_streams.
            * specialize (wc_exp_clockof _ vars (Eapp f es er a) HwcG Hwenv) as Hwcck; simpl in *.
              eapply Forall_impl; [|eapply Hwcck]; intros. 2:econstructor; eauto.
              eapply wc_clock_incl; [|eauto].
              apply incl_appr', incl_map, incl_app, incl_app; auto.
      Qed.

      Corollary sem_rhs_restrict : forall vars anons H b e vs,
          wc_env vars ->
          incl (anon_in e) anons ->
          Forall (fun ck => In ck (map snd vars)) (clockof e) ->
          Forall (fun '(ck, ox) => LiftO True (fun x => InMembers x vars) ox) (nclockof e) ->
          wc_exp G vars e ->
          sem_exp_ck H b e vs ->
          sem_exp_ck (Env.restrict H (List.map fst vars ++ List.map fst anons)) b e vs.
      Proof with eauto.
        intros * Hwenv Hincl Hck Hnck Hwc Hsem.
        destruct e; try solve [eapply sem_exp_restrict; eauto].
        inv Hwc. inv Hsem. simpl in *.
        eapply incl_app' in Hincl as (Hincl1&Hincl2).
        econstructor...
        + eapply Forall2_impl_In; [|eauto]; intros. rewrite Forall_forall in *...
          eapply sem_exp_restrict... etransitivity; [|eapply Hincl1].
          intros ??. eapply in_flat_map...
        + eapply Forall2_impl_In; [|eauto]; intros. rewrite Forall_forall in *...
          eapply sem_exp_restrict... etransitivity; [|eapply Hincl2].
          intros ??. eapply in_flat_map...
        + rewrite <-map_fst_idck, <-map_app. eapply clocked_app_restrict; eauto.
          * intros ? Hin. rewrite InMembers_app. left.
            eapply InMembers_In in Hin as (?&Hin).
            eapply map_filter_In' in Hin as ((?&[|])&Hin&Hf); inv Hf.
            eapply Forall_forall in Hnck; eauto; auto.
          * eapply Forall_impl; [|eauto]. intros.
            eapply in_map_iff in H0 as ((?&?)&?&?); subst.
            eapply wc_clock_incl, wc_env_var; eauto. solve_incl_app.
      Qed.

      Lemma sem_equation_restrict : forall vars anons H b eq,
          wc_env vars ->
          incl (anon_in_eq eq) anons ->
          wc_equation G vars eq ->
          sem_equation_ck H b eq ->
          sem_equation_ck (Env.restrict H (List.map fst vars ++ List.map fst anons)) b eq.
      Proof with eauto.
        unfold anon_in_eq, anon_ins.
        intros vars anons H b [xs es] Hwenv Hincl Hwc Hsem.
        destruct Hwc as (?&?&?). inv Hsem. simpl in *.
        econstructor.
        - eapply Forall2_impl_In; [|eauto]; intros. rewrite Forall_forall in *.
          eapply sem_rhs_restrict...
          + etransitivity; [|eauto]. intros ??. eapply in_flat_map...
          + eapply Forall_incl; [|intros ??; eapply in_flat_map;eauto].
            eapply Forall2_ignore1 in H2. eapply Forall_impl; [|eauto].
            intros ? (?&?&?). eapply in_map_iff. do 2 esplit; eauto; auto.
          + eapply Forall_incl; [|intros ??; eapply in_flat_map;eauto].
            eapply Forall2_ignore1 in H1. eapply Forall2_ignore2 in H2. eapply Forall_impl; [|eauto].
            intros (?&[|]) (?&?&?); simpl in *; auto; subst.
            eapply Forall_forall in H2 as (?&?&?)...
            eapply In_InMembers...
        - eapply Forall2_impl_In; [|eauto]; intros.
          eapply sem_var_restrict...
          eapply Forall2_ignore2, Forall_forall in H2 as (?&?&?); eauto.
          eapply in_app_iff, or_introl, in_map_iff; do 2 esplit; eauto. reflexivity.
      Qed.

      Fact sc_vars_restrict : forall locs vars H' bs,
          incl (map fst locs) (map fst vars) ->
          Forall (wc_clock vars) (map snd locs) ->
          sc_vars locs H' bs ->
          sc_vars locs (Env.restrict H' (map fst vars)) bs.
      Proof.
        intros * Hincl Hwc Hsc.
        eapply Forall_impl_In; [|eauto]; intros (?&?) Hin (xs&Hv&Hck).
        exists xs. split.
        - eapply sem_var_restrict; [|eauto].
          eapply Hincl, in_map_iff. do 2 esplit; eauto; auto.
        - eapply sem_clock_restrict; [|eauto].
          eapply Forall_forall in Hwc; eauto.
          eapply in_map_iff. do 2 esplit; eauto; auto.
      Qed.

      Lemma sem_block_restrict : forall blk anons vars H b,
          wc_env vars ->
          incl (local_anon_in_block blk) anons ->
          wc_block G vars blk ->
          sem_block_ck H b blk ->
          sem_block_ck (Env.restrict H (List.map fst vars ++ List.map fst anons)) b blk.
      Proof with eauto.
        induction blk using block_ind2; intros * Hwenv Hincl Hwc Hsem;
          inv Hwc; inv Hsem; simpl in *.
        - (* equation *)
          econstructor.
          eapply sem_equation_restrict...
        - (* reset *)
          eapply incl_app' in Hincl as (Hincl1&Hincl2).
          econstructor; eauto.
          + eapply sem_exp_restrict...
          + intros k; specialize (H11 k).
            rewrite Forall_forall in *. intros ? Hin.
            eapply sem_block_refines; try eapply H...
            now setoid_rewrite <-Env.restrict_map.
            etransitivity; [|eapply Hincl1].
            intros ??. eapply in_flat_map...
        - (* locals *)
          eapply Slocal with (H':=Env.restrict H' (map fst vars ++ map fst locs ++ map fst anons0 ++ map fst (flat_map local_anon_in_block blocks))).
          + intros * Hsem Hnin1 Hnin2.
            eapply sem_var_restrict_inv in Hsem as (Hin&Hsem).
            eapply sem_var_restrict...
            repeat rewrite in_app_iff in *. destruct Hin as [|[|[|]]]; auto.
            1,2:exfalso.
            * eapply Hnin1, fst_InMembers...
            * eapply Hnin2, fst_InMembers...
          + eapply Env.dom_intro; intros.
            rewrite Env.restrict_In_iff. erewrite Env.dom_use; [|eauto].
            repeat rewrite in_app_iff. repeat rewrite <-fst_InMembers.
            repeat rewrite <-Env.In_Members. rewrite Env.restrict_In_iff.
            repeat rewrite in_app_iff. repeat rewrite <-fst_InMembers.
            split; [intros ([|[|]]&[|[|[|]]])|intros [(?&[|])|[|]]]; auto.
          + rewrite <- map_fst_idty, <-2 map_fst_idck, <-map_fst_idck, <-3 map_app. eapply sc_vars_restrict...
            * repeat rewrite idck_app. solve_incl_app.
            * eapply Forall_impl; [|eauto]; intros.
              eapply wc_clock_incl; [|eauto]. solve_incl_app.
          + rewrite Forall_forall in *; intros.
            rewrite app_assoc, <-map_fst_idty, <-map_fst_idck, <-map_app, <-map_app.
            eapply H...
            * eapply Forall_app; split.
              -- eapply Forall_impl; [|eapply Hwenv]; intros (?&?) ?.
                 eapply wc_clock_incl; [|eauto]; solve_incl_app.
              -- apply Forall_forall; intros (?&?) ?. eapply H5; eauto.
                 eapply in_map_iff; do 2 esplit; eauto.
            * etransitivity; [|eauto].
              intros ??. eapply in_flat_map...
              eapply incl_appr, incl_refl.
      Qed.

    End sem_restrict.

    Hint Constructors Sem.sem_exp Sem.sem_equation Sem.sem_block.

    (** Helper lemmas for induction in the Slocal case *)
    Lemma local_hist_dom : forall xs ys (H H' : Env.t (Stream svalue)),
        Env.dom H xs ->
        Env.dom H' (map fst (Env.elements H) ++ ys) <->
        Env.dom H' (xs ++ ys).
    Proof.
      intros * Hdom1; split; intros Hdom2.
      - eapply Env.dom_intro; intros.
        eapply Env.dom_use in Hdom2. rewrite Hdom2, 2 in_app_iff.
        apply or_iff_compat_r.
        eapply Env.dom_use in Hdom1. now rewrite <-Hdom1, <-fst_InMembers, <-Env.In_Members.
      - eapply Env.dom_intro; intros.
        eapply Env.dom_use in Hdom2. rewrite Hdom2, 2 in_app_iff.
        apply or_iff_compat_r.
        eapply Env.dom_use in Hdom1. now rewrite <-Hdom1, <-fst_InMembers, <-Env.In_Members.
    Qed.

    Lemma local_hist_dom_refines {B C} : forall xs (ys : list (ident * B)) (zs : list (ident * C)) H H',
        (forall x, InMembers x ys \/ InMembers x zs -> ~In x xs) ->
        (forall x vs, sem_var H' x vs -> ~InMembers x ys -> ~InMembers x zs -> sem_var H x vs) ->
        Env.dom H xs ->
        Env.dom H' (map fst (Env.elements H) ++ map fst ys ++ map fst zs) ->
        Env.refines (@EqSt _) H H'.
    Proof.
      intros * Hnd Hinv Hdom1 Hdom2 ?? Hfind.
      erewrite local_hist_dom in Hdom2; eauto.
      assert (Env.In x H) as Hin by (econstructor; eauto).
      eapply Env.dom_use in Hin; eauto.
      assert (In x (xs ++ map fst ys ++ map fst zs)) as Hin' by (apply in_or_app; auto).
      eapply Env.dom_use in Hin'; eauto. destruct Hin' as (v'&Hfind2).
      assert (sem_var H' x v') as Hvar' by (econstructor; eauto; reflexivity).
      eapply Hinv in Hvar'. inv Hvar'. 2,3:(intro contra; eapply Hnd; eauto).
      rewrite H1 in Hfind; inv Hfind.
      do 2 eexists; eauto. now symmetry.
    Qed.

  End ClockedSemantics.

  (** Morphism properties *)

  Hint Constructors sem_exp.

  Add Parametric Morphism env : (sc_vars env)
      with signature Env.Equiv (@EqSt _) ==> @EqSt bool ==> Basics.impl
        as sc_vars_morph.
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

  Add Parametric Morphism {PSyn prefs} (G : @global PSyn prefs) : (sem_exp_ck G)
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

  Add Parametric Morphism {PSyn prefs} (G : @global PSyn prefs) : (sem_equation_ck G)
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

  Add Parametric Morphism {PSyn prefs} (G : @global PSyn prefs) : (sem_block_ck G)
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
    - eapply Slocal with (H'1:=H'); eauto.
      + intros. rewrite <-H6; eauto.
      + eapply Env.dom_intro; intros. eapply Env.dom_use in H2.
        rewrite H2. rewrite 2 in_app_iff. apply or_iff_compat_r.
        now rewrite <-2 fst_InMembers, <-2 Env.In_Members, H6.
      + now rewrite <-H7.
      + rewrite Forall_forall in *; intros; eauto.
        eapply H5; eauto. reflexivity.
  Qed.

  Add Parametric Morphism {PSyn prefs} (G : @global PSyn prefs) : (sem_node_ck G)
      with signature eq ==> @EqSts svalue ==> @EqSts svalue ==> Basics.impl
        as sem_node_ck_morph.
  Proof.
    unfold Basics.impl; intros f xss xss' Exss yss yss' Eyss Sem.
    induction Sem.
    subst.
    econstructor; try reflexivity; eauto.
    + instantiate (1 := H). now rewrite <-Exss.
    + now rewrite <-Eyss.
    + eapply sem_block_ck_morph; eauto. reflexivity.
      now rewrite <-Exss.
    + eapply clocked_node_morph; eauto.
      now rewrite <-Exss.
  Qed.

  (** ** Properties of the [global] environment *)

  Lemma sem_block_ck_cons {PSyn prefs} :
    forall (nd : @node PSyn prefs) nds enums bck Hi bk,
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
                                  -> sem_node_ck (Global enums0 nds) f ins outs). 17:eauto.
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
    - econstructor; eauto.
      rewrite Forall_forall in *; intros.
      eapply H4; eauto.
      contradict H5. constructor. eapply Exists_exists; eauto.
    - rewrite find_node_other with (1:=H7) in H0.
      eapply Snode; eauto.
      eapply H4; eauto.
      apply find_node_later_not_Is_node_in with (1:=Hord) in H0; eauto.
  Qed.

  Corollary sem_node_ck_cons {PSyn prefs} :
    forall (nd : @node PSyn prefs) nds enums f xs ys,
      Ordered_nodes (Global enums (nd::nds))
      -> sem_node_ck (Global enums (nd::nds)) f xs ys
      -> nd.(n_name) <> f
      -> sem_node_ck (Global enums nds) f xs ys.
  Proof.
    intros * Hord Hsem Hnf. inv Hsem.
    rewrite find_node_other with (1:=Hnf) in H0.
    econstructor; eauto.
    eapply sem_block_ck_cons; eauto.
    apply find_node_later_not_Is_node_in with (1:=Hord) in H0; eauto.
  Qed.

  Lemma sem_block_ck_cons' {PSyn prefs} :
    forall (nd : @node PSyn prefs) nds enums bck Hi bk,
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
                                  -> sem_node_ck (Global enums0 (nd::nds)) f ins outs). 17:eauto.
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
    - econstructor; eauto.
      rewrite Forall_forall in *; intros.
      eapply H4; eauto.
      contradict H5. constructor. eapply Exists_exists; eauto.
    - assert (~ Is_node_in_block (n_name nd) (n_block n)) as Hnin.
      { apply find_node_later_not_Is_node_in with (1:=Hord) in H0; auto. }
      rewrite <-find_node_other with (1:=H7) in H0.
      eapply Snode; eauto.
  Qed.

  Corollary sem_node_ck_cons' {PSyn prefs} :
    forall (nd : @node PSyn prefs) nds enums f xs ys,
      Ordered_nodes (Global enums (nd::nds))
      -> sem_node_ck (Global enums nds) f xs ys
      -> nd.(n_name) <> f
      -> sem_node_ck (Global enums (nd::nds)) f xs ys.
  Proof.
    intros * Hord Hsem Hnf. inv Hsem.
    econstructor; eauto.
    - erewrite find_node_other; eauto.
    - eapply sem_block_ck_cons'; eauto.
    apply find_node_later_not_Is_node_in with (1:=Hord) in H0; auto.
  Qed.

  Lemma sem_node_ck_cons_iff {PSyn prefs} :
    forall (n : @node PSyn prefs) nds enums f xs ys,
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

  (* Go back from clocked semantics to semantics *)
  Section sem_ck_sem.
    Context {PSyn : block -> Prop}.
    Context {prefs: PS.t}.
    Variable G : @global PSyn prefs.

    Hypothesis (HwG : wc_global G).

    Lemma sem_exp_ck_sem_exp' : forall H b e vs,
        (forall f ins outs, sem_node_ck G f ins outs -> sem_node G f ins outs) ->
        sem_exp_ck G H b e vs ->
        sem_exp G H b e vs.
    Proof.
      induction e using exp_ind2; intros * Hnodes Hsem; inv Hsem;
        econstructor; eauto.
      1-6,8-10:rewrite Forall_forall in *; eapply Forall2_impl_In; [|eauto]; eauto.
      - (* merge *)
        intros ?? Hin1 Hin2 ?.
        specialize (H0 _ Hin1). rewrite Forall_forall in *.
        eapply Forall2_impl_In; [|eauto]; eauto.
      - (* case *)
        eapply Forall2_impl_In; [|eapply H10]. intros ?? Hin1 Hin2 ?? Hsome; subst.
        eapply Forall_forall in H0; eauto. simpl in H0.
        rewrite Forall_forall in *.
        eapply Forall2_impl_In; [|eauto]; eauto.
    Qed.

    Lemma sem_block_ck_sem_block' : forall blk env H bs,
        (forall f ins outs, sem_node_ck G f ins outs -> sem_node G f ins outs) ->
        NoDup (map fst env ++ map fst (anon_in_block blk)) ->
        NoDupLocals (map fst env ++ map fst (anon_in_block blk)) blk ->
        wc_block G env blk ->
        sem_block_ck G H bs blk ->
        sem_block G H bs blk.
    Proof.
      induction blk using block_ind2; intros * Hg Hnd1 Hnd2 Hwc Hsem;
        inv Hnd2; inv Hwc; inv Hsem; simpl in *.
      - (* equation *)
        inv H5. destruct H2 as (?&?&?). econstructor; eauto. econstructor; eauto.
        eapply Forall2_impl_In; [|eauto]; intros.
        rewrite Forall_forall in *.
        eapply sem_exp_ck_sem_exp'; eauto.
      - (* reset *)
        rewrite Forall_forall in *.
        econstructor; eauto.
        + eapply sem_exp_ck_sem_exp'; eauto.
        + intros k. specialize (H12 k). rewrite Forall_forall in *; intros; eauto.
          eapply H; eauto.
          * eapply nodup_app_map_flat_map; eauto. solve_NoDup_app.
          * eapply NoDupLocals_incl; [|eauto]; simpl.
            rewrite map_app. apply incl_appr', incl_appl, incl_map.
            intros ??. apply in_flat_map; eauto.
      - (* local *)
        eapply Sem.Slocal with (H'0:=Env.restrict H' (map fst (env0 ++ idck (idty locs)))).
        + intros ?? Hvar Hnin.
          eapply sem_var_restrict_inv in Hvar as (Hvar&Hin).
          eapply H9; eauto.
          rewrite map_app, map_fst_idck, map_fst_idty, in_app_iff in Hvar. destruct Hvar as [Hvar|Hvar].
          * intro contra. eapply NoDup_app_In in Hnd1; eauto.
            eapply Hnd1, fst_InMembers; eauto.
            eapply InMembers_incl; [|eauto]. eapply local_anons_in_block_incl.
          * eapply fst_InMembers in Hvar. congruence.
        + rewrite Forall_forall in *; intros.
          eapply Sem.sem_block_restrict; [|eauto]; eauto.
          eapply H; eauto.
          * eapply nodup_app_map_flat_map; eauto.
            rewrite map_app, <-app_assoc, (Permutation_app_comm (map fst (idck _))), app_assoc.
            apply NoDup_app'; auto. rewrite map_fst_idck, map_fst_idty, <-fst_NoDupMembers; auto.
            eapply Forall_forall; intros. rewrite map_fst_idck, map_fst_idty, <-fst_InMembers.
            intro contra. eapply H6 in contra; eauto.
          * eapply NoDupLocals_incl; eauto.
            rewrite map_app, map_fst_idck, map_fst_idty, <-2 app_assoc, (Permutation_app_comm _ (map fst locs)).
            rewrite 2 app_assoc. apply incl_app; [solve_incl_app|apply incl_appr, incl_map].
            intros ??. apply in_flat_map; eauto.
    Qed.

  End sem_ck_sem.

  Lemma sem_node_ck_sem_node PSyn prefs : forall (G : @global PSyn prefs) f ins outs,
      wc_global G ->
      sem_node_ck G f ins outs ->
      sem_node G f ins outs.
  Proof.
    intros (enums&nodes) ??? Hwc.
    assert (Ordered_nodes (Global enums nodes)) as Hord.
    { eapply wl_global_Ordered_nodes; eauto. }
    revert f ins outs.
    induction nodes; intros * Hsem. now inversion Hsem.
    assert (Hsem' := Hsem).
    inversion_clear Hsem' as [?????? Hfind Hins Houts Heqs Hblk].
    pose proof (Lord.find_node_not_Is_node_in _ _ _ Hord Hfind) as Hnini.
    simpl in Hfind. destruct (ident_eq_dec (n_name a) f).
    - rewrite find_node_now in Hfind; auto. inv Hfind.
      econstructor; eauto. rewrite find_node_now; auto.
      eapply sem_block_cons'; eauto.
      eapply sem_block_ck_cons in Heqs; eauto.
      eapply sem_block_ck_sem_block'; eauto.
      + inv Hwc; inv Hord; eauto.
      + erewrite map_fst_idck, <-map_app, <-fst_NoDupMembers. eapply n_nodup.
      + erewrite map_fst_idck, map_fst_idty. eapply n_nodup.
      + inv Hwc. destruct H3 as (Hwn&?); simpl in Hwn. eapply Hwn.
    - rewrite find_node_other in Hfind; eauto.
      eapply sem_node_ck_cons in Hsem; eauto.
      eapply sem_node_cons'; eauto.
      inv Hwc. inv Hord. eapply IHnodes; eauto.
  Qed.

  Lemma sem_exp_ck_sem_exp {PSyn prefs} (G: @global PSyn prefs) : forall H b e vs,
      wc_global G ->
      sem_exp_ck G H b e vs ->
      sem_exp G H b e vs.
  Proof.
    intros.
    eapply sem_exp_ck_sem_exp'; eauto.
    intros. eapply sem_node_ck_sem_node; eauto.
  Qed.

  Corollary sem_exps_ck_sem_exps {PSyn prefs} (G: @global PSyn prefs) : forall H b es vs,
      wc_global G ->
      Forall2 (sem_exp_ck G H b) es vs ->
      Forall2 (sem_exp G H b) es vs.
  Proof.
    intros.
    eapply Forall2_impl_In; [|eauto]; intros.
    eapply sem_exp_ck_sem_exp; eauto.
  Qed.

  (** Build the alignment proof *)

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

  Hint Constructors Is_free_in_clock.

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

  Fact sc_has_base {PSyn prefs} : forall H b bck sub (n : @node PSyn prefs) ncks ss,
      wc_env (idck (idty (n_in n))) ->
      Forall2 (fun nck => sem_clock H b (stripname nck)) ncks (map abstract_clock ss) ->
      Forall2 (WellInstantiated bck sub) (idck (idty (n_in n))) ncks ->
      sem_clock H b bck (clocks_of ss).
  Proof.
    intros * WCin Hscin WIi.
    pose proof (wc_env_has_Cbase _ WCin) as [i Hin].
    { rewrite length_idck, length_idty. exact (n_ingt0 n). }
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
  Corollary sc_inside_mask {PSyn prefs} :
    forall H Hi b es ss0 bck sub (n : @node PSyn prefs) k rs,
      Forall2 (fun '(_, o) (s : Stream svalue) => LiftO True (fun x1 : ident => sem_var H x1 s) o) (nclocksof es) (concat ss0) ->
      wc_env (idck (idty (n_in n))) ->
      Forall2 (sem_clock H b) (clocksof es) (map abstract_clock (concat ss0)) ->
      Forall2 (WellInstantiated bck sub) (idck (idty (n_in n))) (nclocksof es) ->
      Forall2 (sem_var Hi) (idents (n_in n)) (map (maskv k rs) (concat ss0)) ->
      Forall2 (fun xc => sem_clock Hi (clocks_of (map (maskv k rs) (concat ss0))) (snd xc))
              (idck (idty (n_in n))) (map abstract_clock (map (maskv k rs) (concat ss0))).
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
      rewrite map_fst_idck, map_fst_idty, Forall2_map_2; eauto.
  Qed.

  Definition def_stream b := enum b 0.

  Lemma sc_outside_mask {PSyn1 PSyn2 prefs1 prefs2} :
    forall (G : @global PSyn1 prefs1) H es b env ncks ss0 ss bck sub (n : @node PSyn2 prefs2) rs,
      Forall (wc_exp G env) es ->
      Forall2 (fun '(_, o1) s => LiftO True (fun x0 : ident => sem_var H x0 s) o1) (nclocksof es) (concat ss0) ->
      Forall2 (fun '(_, o) s => LiftO True (fun x0 => sem_var H x0 s) o) ncks ss ->
      wc_env (idck (idty (n_in n))) ->
      wc_env (idck (idty (n_in n ++ n_out n))) ->
      Forall2 (sem_clock H b) (clocksof es) (map abstract_clock (concat ss0)) ->
      Forall2 (WellInstantiated bck sub) (idck (idty (n_in n))) (nclocksof es) ->
      Forall2 (WellInstantiated bck sub) (idck (idty (n_out n))) ncks ->
      (forall k, exists Hi,
            Forall2 (fun xc => sem_clock Hi (clocks_of (map (maskv k rs) (concat ss0))) (snd xc))
                    (idck (idty (n_out n))) (map abstract_clock (map (maskv k rs) ss)) /\
            Forall2 (sem_var Hi) (idents (n_in n)) (map (maskv k rs) (concat ss0)) /\
            Forall2 (sem_var Hi) (idents (n_out n)) (map (maskv k rs) ss)) ->
      Forall2 (sem_clock H b) (map fst ncks) (map abstract_clock ss).
  Proof.
    intros * Hwc Hsvar Hse2 WCin WCinout Hscin WIi WIo Hk.

    rewrite clocksof_nclocksof, Forall2_map_1, Forall2_map_2 in Hscin.
    rewrite Forall2_map_1, Forall2_map_2.
    assert (length ncks = length (idck (idty (n_out n)))) as Hlen1.
    { now apply Forall2_length in WIo. }
    assert (length ncks = length ss) as Hlen2.
    { specialize (Hk 0) as (?&_&_&Hf).
      rewrite Forall2_map_2, idck_idents, Forall2_map_1 in Hf.
      apply Forall2_length in Hf. rewrite length_idck in Hf.
      setoid_rewrite Hlen1; auto. now rewrite length_idck, length_idty. }
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
        destruct (nth n0 (idck (idty (n_out n))) (1%positive, Cbase)) as (yck, ny) eqn:Hy.
        assert (In (yck, ny) (idck (idty (n_in n ++ n_out n)))) as Hyin2.
        { rewrite idty_app, idck_app. apply in_or_app. right.
          rewrite <- Hy. apply nth_In. congruence. }
        pose proof (wc_env_free_in_clock _ _ _ _ WCinout Hyin2 Free) as [].
        eapply inst_in_eqst_mask with (vs:=(concat ss0++ss)). 1,5:eauto.
        * rewrite idty_app, idck_app. eapply Forall2_app; eauto.
        * rewrite map_fst_idck, map_fst_idty, map_app, map_app.
          eapply Forall2_app; eauto.
        * eapply Forall2_app; eauto.
  Qed.

  Definition sem_clock_inputs {PSyn prefs} (G : @global PSyn prefs) (f : ident) (xs : list (Stream svalue)): Prop :=
    exists H n,
      find_node f G = Some n /\
      Forall2 (sem_var H) (idents (n_in n)) xs /\
      Forall2 (fun xc => sem_clock H (clocks_of xs) (snd xc))
              (idck (idty (n_in n))) (map abstract_clock xs).

  Lemma sem_clock_inputs_cons {PSyn prefs} :
    forall enums (nodes : list (@node PSyn prefs)) f n ins,
      n_name n <> f ->
      sem_clock_inputs (Global enums nodes) f ins <-> sem_clock_inputs (Global enums (n :: nodes)) f ins.
  Proof.
    intros * Hname.
    split; intros (H & n' & Hfind &?&?);
      exists H, n'; repeat split; auto.
    - rewrite find_node_other; eauto.
    - erewrite <- find_node_other; eauto.
  Qed.

  Lemma inputs_clocked_vars {PSyn prefs} :
    forall enums (nodes : list (@node PSyn prefs)) n H f ins,
      sem_clock_inputs (Global enums (n :: nodes)) f ins ->
      n_name n = f ->
      wc_env (idck (idty (n_in n))) ->
      Forall2 (sem_var H) (idents (n_in n)) ins ->
      Forall2 (fun xc => sem_clock H (clocks_of ins) (snd xc)) (idck (idty (n_in n))) (map abstract_clock ins).
  Proof.
    intros * (H'&n'& Hfind & Hv & Hscin) Hnf Wcin Hins; subst.
    rewrite find_node_now in Hfind; auto. inv Hfind.
    pose proof (sem_var_env_eq _ _ _ _ Hins Hv) as Horel.
    rewrite idck_idents in *. rewrite Forall2_map_1 in Hv, Hins.
    rewrite map_fst_idck, <-map_fst_idty, <-map_fst_idck in Horel.
    eapply Forall2_impl_In; [|eauto]. intros; simpl in *.
    eapply sem_clock_same_find; eauto.
    unfold wc_env in Wcin. eapply Forall_forall in H0; [|eauto]. auto.
  Qed.

  Lemma sem_clocks_det : forall H H' b ins outs vins vouts ss,
      wc_env (idck (idty (ins ++ outs))) ->
      Forall2 (sem_var H) (idents ins) vins ->
      Forall2 (sem_var H) (idents outs) vouts ->
      Forall2 (sem_var H') (idents ins) vins ->
      Forall2 (sem_var H') (idents outs) vouts ->
      Forall2 (fun xc => sem_clock H b (snd xc)) (idck (idty outs)) ss ->
      Forall2 (fun xs => sem_clock H' b (snd xs)) (idck (idty outs)) ss.
  Proof.
    intros * Hwc Hi1 Ho1 Hi2 Ho2 Hck.
    eapply Forall2_impl_In; [|eauto]. intros [? ?] ? Hin1 Hin2 Hsc.
    rewrite idty_app, idck_app in Hwc. assert (Hwc':=Hwc). apply Forall_app_weaken in Hwc.
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
                   (idck (idty ins) ++ idck (idty outs))) as Hvars.
    { rewrite <-idck_app, <-idty_app. eapply Forall_map, Forall_map.
      eapply Forall2_Forall2 in Ho; [|eapply Ho']. clear Ho'.
      eapply Forall2_ignore2 in Ho.
      eapply Forall_impl; [|eauto]. intros (?&(?&?)&?) (?&?&?&?).
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
                (idck (idty (n_in n))) (map abstract_clock xs) ->
        Forall2 (fun xc => sem_clock H (clocks_of xs) (snd xc))
                (idck (idty (n_out n))) (map abstract_clock os).
    Proof.
      intros * Hwc Hsem Hfind Hins Houts Hckins.
      eapply Hnode in Hsem. 2:(repeat esplit; eauto).
      destruct Hwc as (_&Hwc&_). inv Hsem.
      rewrite Hfind in H1. inv H1.
      eapply sem_clocks_det; eauto.
      rewrite Forall2_map_2.
      unfold idck, idty, idents in *.
      rewrite Forall2_map_1 in H3. rewrite Forall2_map_1, Forall2_map_1.
      eapply Forall2_impl_In; [|eauto]; intros (?&?&?) ? Hin1 Hin2 Hvar; simpl in *.
      destruct H6 as (_&Hinv).
      eapply Forall_map, Forall_map, Forall_forall in Hinv as (?&Hvar'&Hck'); eauto using in_or_app.
      eapply sem_var_det in Hvar; eauto.
      rewrite <-Hvar; auto.
    Qed.

    Definition sc_var_inv env (H : history) (b : Stream bool) : ident -> Prop :=
      fun cx => forall x ck xs,
          In (x, (ck, cx)) env ->
          sem_var H x xs ->
          sem_clock H b ck (abstract_clock xs).

    Lemma sc_vars_sc_var_inv : forall env H b,
        NoDupMembers env ->
        NoDup (map snd (idck env)) ->
        sc_vars (idty env) H b ->
        Forall (sc_var_inv env H b) (map snd (idck env)).
    Proof.
      intros * Hnd1 Hnd2 Hinv'.
      unfold sc_vars in Hinv'. unfold idty, idck in *.
      rewrite Forall_map in Hinv'. repeat rewrite Forall_map.
      eapply Forall_impl_In; [|eauto].
      intros (?&?&?) Hin (?&Hvar&Hck) ??? Hin' Hvar'; simpl in *.
      assert (x0 = i); subst.
      { eapply NoDup_snd_det; eauto. 1,2:eapply in_map_iff; do 2 esplit.
        2:eapply Hin'. 3:eapply Hin. 1,2:reflexivity. }
      eapply sem_var_det in Hvar; eauto. rewrite Hvar.
      assert (c = ck); subst; auto.
      eapply NoDupMembers_det in Hnd1; [|eapply Hin|eapply Hin'].
      now inv Hnd1.
    Qed.

    Lemma sc_var_inv_sc_vars : forall env H b,
        Forall (fun x => exists v, sem_var H x v) (map fst env) ->
        Forall (sc_var_inv env H b) (map snd (idck env)) ->
        sc_vars (idty env) H b.
    Proof.
      intros * Hvars Hinv.
      unfold sc_vars.
      unfold idck in Hinv. repeat rewrite Forall_map in Hinv. rewrite Forall_map in Hvars.
      eapply Forall_map. rewrite Forall_forall in *.
      intros (?&?&?) Hin. edestruct Hvars as (?&Hvar); eauto. simpl in *.
      do 2 eexists; eauto.
      eapply Hinv; eauto.
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
        P_exps (sc_exp_inv env H b) es k ->
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
        (forall k, k < length (annots es) -> P_exps (sc_exp_inv env H b) es k) ->
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

    Lemma sc_exp_var : forall env H b x cx ann,
        NoDupMembers env ->
        In (x, cx) (idck env) ->
        sc_var_inv env H b cx ->
        sc_exp_inv (idty env) H b (Evar x ann) 0.
    Proof.
      intros * Hnd(* 1 Hnd2 *) Hin Hvar ss Hwc Hsem _; inv Hsem; simpl.
      eapply Hvar; [|eauto].
      assert (In (x, clock_of_nclock ann0) (idty env0)) as Hin' by (inv Hwc; auto).
      eapply in_map_iff in Hin as ((?&?&?)&Heq&Hin); inv Heq.
      eapply in_map_iff in Hin' as ((?&?&?)&Heq&Hin'); inv Heq.
      eapply NoDupMembers_det in Hin; eauto. inv Hin; auto.
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
        P_exps (sc_exp_inv env H b) e0s k ->
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
        P_exps (sc_exp_inv env H b) e0s k ->
        P_exps (sc_exp_inv env H b) es k ->
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

    Lemma sc_exp_when : forall env H b es x cx b' ann k,
        NoDupMembers env ->
        k < length (fst ann) ->
        P_exps (sc_exp_inv (idty env) H b) es k ->
        In (x, cx) (idck env) ->
        sc_var_inv env H b cx ->
        sc_exp_inv (idty env) H b (Ewhen es x b' ann) k.
    Proof.
      intros * Hnd Hk Hes Hin Hvar ss Hwc Hsem Hanon; simpl.
      inv Hwc. inv Hsem. inv Hanon.
      eapply P_exps_sc_exp_inv in Hes; eauto.
      assert (Hv:=H13). eapply Hvar in Hv; eauto.
      2:{ eapply in_map_iff in Hin as ((?&?&?)&Heq&Hin); inv Heq.
          eapply in_map_iff in H4 as ((?&?&?)&Heq&Hin'); inv Heq.
          eapply NoDupMembers_det in Hin; eauto. inv Hin; eauto.
      }
      erewrite map_nth' with (d':=OpAux.bool_velus_type); eauto.
      unfold clock_of_nclock, stripname; simpl.
      eapply Forall_forall in H6. 2:eapply nth_In; rewrite <- H7; eauto.
      eapply sc_when in Hes; eauto. erewrite H6; eauto.
      eapply Forall2_forall2 in H14 as [_ Hwhen].
      eapply Hwhen; eauto.
      replace (length (concat ss0)) with (length (annots es)). rewrite <- length_clocksof_annots, <- H7; eauto.
      symmetry. eapply sem_exps_numstreams; eauto.
    Qed.

    Lemma sc_exp_merge : forall env H b x cx tx es ann k,
        NoDupMembers env ->
        k < length (fst ann) ->
        In (x, cx) (idck env) ->
        sc_var_inv env H b cx ->
        Forall (fun es => P_exps (sc_exp_inv (idty env) H b) es k) es ->
        sc_exp_inv (idty env) H b (Emerge (x, tx) es ann) k.
    Proof.
      intros * Hnd Hk Hin Hvar Hes ss Hwc Hsem Hanon; simpl.
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
        Forall (LiftO (P_exps (sc_exp_inv env H b) d k)
                      (fun es => P_exps (sc_exp_inv env H b) es k)) es ->
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
        (forall k0 : nat, k0 < length (annots es) -> P_exps (sc_exp_inv env H b) es k0) ->
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

    Lemma sc_exp_equation : forall env H b xs es k cx,
        NoDup (map snd (idck env)) ->
        NoDupMembers env ->
        k < length xs ->
        wc_equation G (idty env) (xs, es) ->
        Sem.sem_equation G H b (xs, es) ->
        anon_sem_equation G H b (xs, es) ->
        P_exps (sc_exp_inv (idty env) H b) es k ->
        In (nth k xs xH, cx) (idck env) ->
        sc_var_inv env H b cx.
    Proof.
      intros * Hnd1 Hnd2 Hk Hwc Hsem Hanon Hexps Hin ??? Hin' Hvar.
      destruct Hwc as (Hwc1&_&Hwc2). inv Hsem.
      assert (x = nth k xs xH) by (eapply NoDup_snd_det; eauto); subst.
      eapply P_exps_sc_exp_inv in Hexps; eauto.
      assert (nth k (clocksof es) Cbase = ck); subst.
      { eapply Forall2_forall2 in Hwc2 as [_ HIn'].
        specialize (HIn' xH Cbase _ _ _ Hk eq_refl eq_refl).
        eapply NoDupMembers_det in HIn'; eauto. eapply NoDupMembers_idty; eauto.
        eapply in_map_iff; do 2 esplit; eauto. reflexivity.
      }
      assert (xs0 ≡ nth k (concat ss) (def_stream b)) as Hequiv.
      { eapply Forall2_forall2 in H6 as [_ Hvar'].
        specialize (Hvar' xH (def_stream b) _ _ _ Hk eq_refl eq_refl).
        eapply sem_var_det in Hvar'; eauto. }
      rewrite Hequiv; auto.
    Qed.

    Lemma sc_exp' : forall env H b e k,
        NoDupMembers env ->
        wc_global G ->
        wc_exp G (idty env) e ->
        k < numstreams e ->
        (forall cx, Is_free_left (idck env) cx k e -> sc_var_inv env H b cx) ->
        sc_exp_inv (idty env) H b e k.
    Proof.
      intros * Hnd Hsc Hwc Hnum Hfree.
      eapply exp_causal_ind
             with (P_exp:=sc_exp_inv _ H b); eauto; intros.
      - apply sc_exp_const.
      - apply sc_exp_enum.
      - eapply sc_exp_var; eauto.
      - apply sc_exp_unop; auto.
      - apply sc_exp_binop; auto.
      - apply sc_exp_fby; auto.
      - apply sc_exp_arrow; auto.
      - eapply sc_exp_when; eauto.
      - eapply sc_exp_merge; eauto.
      - apply sc_exp_case; auto.
      - eapply sc_exp_app; eauto.
      - eapply wc_exp_wx_exp in Hwc. rewrite map_fst_idty in Hwc. now rewrite map_fst_idck.
    Qed.

    Lemma sem_var_refines_iff : forall dom H H' x v,
        Env.refines (@EqSt _) H H' ->
        Env.dom_lb H dom ->
        In x dom ->
        sem_var H x v <-> sem_var H' x v.
    Proof.
      intros * Href Hdom Hin; split; intros Hvar.
      - eapply sem_var_refines; eauto.
      - eapply sem_var_refines'; eauto.
    Qed.

    Lemma sem_clock_refines_iff : forall dom H H' ck bs bs',
        Env.refines (@EqSt _) H H' ->
        Env.dom_lb H dom ->
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
            setoid_rewrite <-Env.dom_lb_map; eauto.
        + econstructor; eauto.
          * eapply sem_var_refines_iff; eauto.
          * eapply CoFix. 3,4:eauto. eapply history_tl_refines; eauto.
            setoid_rewrite <-Env.dom_lb_map; eauto.
        + eapply Son_abs2; eauto.
          * eapply sem_var_refines_iff; eauto.
          * eapply CoFix. 3,4:eauto. eapply history_tl_refines; eauto.
            setoid_rewrite <-Env.dom_lb_map; eauto.
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

    Lemma sc_var_inv_mask : forall env H b x r k,
        sc_var_inv env H b x ->
        sc_var_inv env (mask_hist k r H) (maskb k r b) x.
    Proof.
      intros * Hinv ??? Hin Hvar.
      eapply sem_var_mask_inv in Hvar as (?&Hvar&Heq).
      rewrite Heq, ac_mask.
      eapply sem_clock_mask.
      eapply Hinv; eauto.
    Qed.

    Lemma sc_var_inv_unmask : forall env H b x r,
      (forall k : nat, sc_var_inv env (mask_hist k r H) (maskb k r b) x) ->
      sc_var_inv env H b x.
    Proof.
      intros * Hinv ??? Hin Hvar.
      eapply sem_clock_unmask with (r:=r). intros k.
      rewrite <-ac_mask. eapply Hinv; eauto.
      eapply sem_var_mask; eauto.
    Qed.

    Definition idckcaus {A} (xs : list (ident * (A * clock * ident))) :=
      map (fun '(x, (_, ck, cx)) => (x, (ck, cx))) xs.

    Lemma idckcaus_app {A} : forall (xs1 xs2 : list (ident * (A * clock * ident))),
        idckcaus (xs1 ++ xs2) = idckcaus xs1 ++ idckcaus xs2.
    Proof. unfold idckcaus. apply map_app. Qed.

    Lemma map_fst_idckcaus {A} : forall (xs : list (ident * (A * clock * ident))),
        map fst (idckcaus xs) = map fst xs.
    Proof.
      intros. unfold idckcaus.
      rewrite map_map.
      eapply map_ext. intros (?&((?&?)&?)); auto.
    Qed.

    Section sem_block_ck'.

      Inductive sem_block_ck' (envP : list ident) : history -> Stream bool -> block -> Prop :=
      | Sckbeq : forall Hi bs eq,
          sem_equation G Hi bs eq ->
          sem_block_ck' envP Hi bs (Beq eq)
      | Sckreset : forall Hi bs blocks er sr r,
          sem_exp G Hi bs er [sr] ->
          bools_of sr r ->
          (forall k, Forall (sem_block_ck' envP (mask_hist k r Hi) (maskb k r bs)) blocks) ->
          sem_block_ck' envP Hi bs (Breset blocks er)
      | Scklocal : forall Hi bs locs blocks Hl,
          (forall x vs, sem_var Hl x vs -> ~(InMembers x locs) -> sem_var Hi x vs) ->
          Forall (sem_block_ck' envP Hl bs) blocks ->
          Forall (fun x =>
                    sc_var_inv (idckcaus locs) (Env.union Hi Hl) bs x)
                 envP ->
          sem_block_ck' envP Hi bs (Blocal locs blocks).

      Lemma sem_block_sem_block_ck' : forall blk Hi bs,
          sem_block G Hi bs blk ->
          sem_block_ck' [] Hi bs blk.
      Proof.
        induction blk using block_ind2; intros * Hsem; inv Hsem.
        - (* equation *)
          constructor; auto.
        - (* reset *)
          econstructor; eauto.
          intros k. specialize (H7 k).
          rewrite Forall_forall in *; eauto.
        - (* locals *)
          eapply Scklocal with (Hl:=H'); eauto.
          rewrite Forall_forall in *; eauto.
      Qed.

      Lemma sem_block_ck'_sem_block : forall envP blk Hi bs,
          sem_block_ck' envP Hi bs blk ->
          sem_block G Hi bs blk.
      Proof.
        induction blk using block_ind2; intros * Hsem; inv Hsem.
        - (* equation *)
          constructor; auto.
        - (* reset *)
          econstructor; eauto.
          intros k. specialize (H6 k).
          rewrite Forall_forall in *; eauto.
        - (* locals *)
          eapply Sem.Slocal with (H':=Hl); eauto.
          rewrite Forall_forall in *; eauto.
      Qed.

      Lemma sem_block_ck'_Perm : forall xs ys blk Hi bs,
          Permutation xs ys ->
          sem_block_ck' xs Hi bs blk ->
          sem_block_ck' ys Hi bs blk.
      Proof.
        induction blk using block_ind2; intros * Hperm Hsem;
          inv Hsem.
        - (* equation *)
          constructor; auto.
        - (* reset *)
          econstructor; eauto.
          intros k. specialize (H6 k).
          rewrite Forall_forall in *; eauto.
        - (* local *)
          econstructor; eauto.
          + rewrite Forall_forall in *; intros * Hin; eauto.
          + rewrite <-Hperm; auto.
      Qed.

      Global Add Parametric Morphism envP : (sem_block_ck' envP)
          with signature (Env.Equiv (@EqSt _) ==> eq ==> eq ==> Basics.impl)
            as sem_block_ck'_Equiv.
      Proof.
        intros Hi1 Hi2 HH bs blk. revert Hi1 Hi2 HH bs.
        induction blk using block_ind2; intros * HH * Hsem; inv Hsem.
        - (* equation *)
          constructor. eapply Sem.sem_equation_refines; [|eauto].
          now rewrite HH.
        - (* reset *)
          econstructor; eauto.
          + eapply Sem.sem_exp_refines; [|eauto]. now rewrite HH.
          + intros k. specialize (H6 k).
            rewrite Forall_forall in *. intros.
            eapply H; eauto.
            eapply Env.map_Equiv; eauto.
            intros ?? Heq. now rewrite Heq.
        - (* locals *)
          eapply Scklocal with (Hl:=Hl); eauto.
          intros. rewrite <-HH; eauto.
          eapply Forall_impl; [|eauto]; intros ? Hsc ??? Hin Hvar.
          rewrite <-HH. eapply Hsc; eauto. rewrite HH; eauto.
      Qed.

      Lemma sem_block_ck'_refines : forall envP blk xs H H' bs,
          VarsDefined blk xs ->
          NoDupLocals xs blk ->
          Env.refines (@EqSt _) H H' ->
          sem_block_ck' envP H bs blk ->
          sem_block_ck' envP H' bs blk.
      Proof.
        induction blk using block_ind2; intros * Hvars Hnd Href Hsem;
          inv Hvars; inv Hnd; inv Hsem.
        - (* equation *)
          constructor; eauto using Sem.sem_equation_refines.
        - (* reset *)
          econstructor; eauto using Sem.sem_exp_refines.
          intros k. specialize (H9 k).
          rewrite Forall_forall in *; intros; eauto.
          eapply Forall2_ignore2, Forall_forall in H4 as (?&?&?); eauto.
          eapply H. 1-3,5:eauto.
          + eapply NoDupLocals_incl; eauto. eapply incl_concat; eauto.
          + eapply Env.refines_map; eauto. intros ?? Heq. now rewrite Heq.
        - (* locals *)
          econstructor; [|eauto|eauto]; eauto using sem_var_refines.
          eapply Forall_impl; [|eauto]; intros ? Hsc ??? Hin Hv.
          eapply sem_clock_refines, Hsc; eauto; simpl in *.
          + intros ?? Hfind.
            eapply Env.union_find4' in Hfind as [(Hfind1&Hfind2)|Hfind2].
            * eapply Href in Hfind1 as (v'&?&?). exists v'; split; auto.
              eapply Env.union_find2; eauto.
            * exists v. split; try reflexivity. eapply Env.union_find3'; eauto.
          + assert (Env.dom_lb Hl (map fst locs)) as Hdom.
            { eapply Env.dom_lb_incl with (ys:=concat xs0). rewrite <-H5. apply incl_appl, incl_refl.
              eapply Env.dom_lb_concat, Forall_forall; eauto; intros ? Hin'.
              eapply Forall2_ignore1, Forall_forall in H3 as (?&?&?); eauto.
              rewrite Forall_forall in *.
              eapply sem_block_dom_lb; eauto using sem_block_ck'_sem_block.
              eapply NoDupLocals_incl; eauto.
              rewrite Permutation_app_comm, H5. eapply incl_concat; eauto. }
            eapply Env.dom_lb_use in Hdom as (?&Hfind).
            2:{ rewrite <-map_fst_idckcaus. eapply in_map_iff; do 2 esplit; eauto. }
            inv Hv. econstructor. eapply Env.union_find3'; eauto.
            eapply Env.union_find3' with (m1:=H') in Hfind. rewrite H2 in Hfind.
            now inv Hfind.
      Qed.

      Lemma sem_block_ck'_restrict : forall envP blk xs vars H bs,
          VarsDefined blk xs ->
          NoDupLocals xs blk ->
          wc_block G vars blk ->
          sem_block_ck' envP H bs blk ->
          sem_block_ck' envP (Env.restrict H (List.map fst vars)) bs blk.
      Proof.
        induction blk using block_ind2; intros * Hvars Hnd Hwc Hsem;
          inv Hvars; inv Hnd; inv Hwc; inv Hsem.
        - (* equation *)
          econstructor.
          eapply Sem.sem_equation_restrict; eauto.
        - (* reset *)
          econstructor; eauto.
          + eapply Sem.sem_exp_restrict; eauto.
          + intros k; specialize (H12 k).
            rewrite Forall_forall in *. intros ? Hin.
            eapply Forall2_ignore2, Forall_forall in H4 as (?&?&?); eauto.
            eapply sem_block_ck'_Equiv; try eapply H; eauto.
            now setoid_rewrite <-Env.restrict_map.
            eapply NoDupLocals_incl; eauto. eapply incl_concat; eauto.
        - (* locals *)
          eapply Scklocal with (Hl:=Env.restrict Hl (List.map fst vars ++ List.map fst locs)); eauto.
          + intros ?? Hvar Hnin.
            eapply sem_var_restrict_inv in Hvar as (Hin&Hvar); eauto.
            eapply sem_var_restrict; eauto.
            apply in_app_iff in Hin as [Hin|Hin]; auto.
            exfalso. eapply Hnin, fst_InMembers; eauto.
          + rewrite Forall_forall in *; intros.
            eapply Forall2_ignore2, Forall_forall in H3 as (?&?&?); eauto.
            rewrite <-map_fst_idty, <-map_fst_idck, <-map_app.
            eapply H; eauto.
            eapply NoDupLocals_incl; eauto.
            rewrite Permutation_app_comm, H5. eapply incl_concat; eauto.
          + rewrite Forall_forall in *. intros * ???? Hin Hvar.
            assert (Env.dom_lb Hl (map fst locs)) as Hdom2.
            { eapply Env.dom_lb_incl with (ys:=concat xs0); [rewrite <-H5; eapply incl_appl, incl_refl|].
              eapply Env.dom_lb_concat.
              rewrite Forall_forall in *. intros.
              eapply Forall2_ignore1, Forall_forall in H3 as (?&Hinblk&Hvars); eauto.
              eapply sem_block_dom_lb; eauto using sem_block_ck'_sem_block.
              eapply NoDupLocals_incl; eauto.
              etransitivity; [eapply incl_concat; eauto|]. rewrite <-H5.
              rewrite Permutation_app_comm. reflexivity.
            }
            assert (Env.refines (@EqSt _)
                                (Env.union (Env.restrict H0 (map fst vars)) (Env.restrict Hl (map fst vars ++ map fst locs)))
                                (Env.union H0 Hl)).
            { intros ?? Hfind.
              eapply Env.union_find4' in Hfind as [(Hfind1&Hfind2)|Hfind2].
              - eapply Env.restrict_find_inv in Hfind1 as (Hin'&Hfind1).
                exists v. split; try reflexivity. eapply Env.union_find2; eauto.
                destruct (Env.find x1 Hl) eqn:Hfind3; eauto.
                eapply Env.restrict_find in Hfind3; try rewrite Hfind2 in Hfind3; try congruence.
                apply in_or_app; auto.
              - eapply Env.restrict_find_inv in Hfind2 as (?&?).
                exists v. split; try reflexivity; eauto using Env.union_find3'.
            }
            eapply sem_var_refines, H14 in Hvar; eauto.
            eapply sem_clock_refines'; [| |eauto].
            * eapply H10. eapply in_map_iff in Hin as ((?&(?&?)&?)&Heq&Hin); inv Heq.
              repeat (eapply in_map_iff; do 2 esplit); eauto. reflexivity.
            * intros ?? Hinm Hvar'. inv Hvar'.
              { eapply Env.union_find4' in H12 as [(Hfind1&Hfind2)|Hfind2].
                - apply InMembers_app in Hinm as [Hinm|Hinm].
                  + econstructor; eauto.
                    eapply Env.union_find2. eapply Env.restrict_find; eauto. eapply fst_InMembers; eauto.
                    eapply Env.restrict_find_None; eauto.
                  + exfalso. eapply Env.dom_lb_use in Hdom2 as (?&Hfind3).
                    * rewrite Hfind3 in Hfind2. congruence.
                    * now rewrite fst_InMembers, map_fst_idck, map_fst_idty in Hinm.
                - econstructor; eauto. eapply Env.union_find3', Env.restrict_find; eauto.
                  now rewrite fst_InMembers, map_app, map_fst_idck, map_fst_idty in Hinm. }
      Qed.
    End sem_block_ck'.

    Fact idty_idckcaus {A} : forall (xs : list (ident * (A * clock * ident))),
        idty (idckcaus xs) = idck (idty xs).
    Proof.
      intros. unfold idty, idck, idckcaus. rewrite 2 map_map.
      eapply map_ext. intros (?&(?&?)&?); eauto.
    Qed.

    Fact idck_idckcaus {A} : forall (xs : list (ident * (A * clock * ident))),
        idck (idckcaus xs) = idcaus xs.
    Proof.
      intros. unfold idck, idcaus, idckcaus. rewrite map_map.
      eapply map_ext. intros (?&(?&?)&?); eauto.
    Qed.

    Lemma union_dom_ub_dom_lb_dom {V} : forall (m1 m2 : Env.t V) xs ys,
        Env.dom m1 xs ->
        Env.dom_lb m2 ys ->
        Env.dom_ub m2 (xs ++ ys) ->
        Env.dom (Env.union m1 m2) (xs ++ ys).
    Proof.
      intros * Hdom1 Hdom2 Hdom3.
      eapply Env.dom_intro; intros.
      rewrite Env.union_In, in_app_iff. erewrite Env.dom_use; eauto.
      split; intros [Hin|Hin]; auto.
      - eapply Env.dom_ub_use, in_app_iff in Hdom3; eauto.
      - eapply Env.dom_lb_use in Hin; eauto.
    Qed.

    Lemma sc_block : forall envP blk env xs Hi bs y cy,
        wc_global G ->
        NoDup (map snd (idck (env ++ idckcaus (locals blk)))) ->
        NoDupMembers (idty env ++ idck (anon_in_block blk)) ->
        NoDupLocals (map fst env ++ map fst (anon_in_block blk)) blk ->
        VarsDefined blk xs ->
        incl xs (map fst env) ->
        wc_env (idty env) ->
        wc_block G (idty env) blk ->
        sem_block_ck' envP Hi bs blk ->
        Env.dom Hi (map fst env) ->
        In y xs ->
        In (y, cy) (idck env) ->
        (forall cx, In cx (map snd (idck env)) -> depends_on (idck env) cy cx blk -> sc_var_inv env Hi bs cx) ->
        (forall cx, In cx (map snd (idcaus (locals blk))) -> depends_on (idck env) cy cx blk -> In cx envP) ->
        sc_var_inv env Hi bs cy.
    Proof.
      induction blk as [(xs&es)| |] using block_ind2;
        intros * HwG Hnd1 Hnd2 Hnd3 Hvars Hincl Henv Hwc Hsem Hdom Hinxs Hinenv Hsc HenvP;
        inv Hnd3; inv Hvars; inv Hwc; inv Hsem; simpl in *.
      - (* equation *)
        assert (Hsem:=H3). eapply sem_equation_anon in H3 as (H'&Href&_&Hanon); eauto.
        2:(rewrite map_fst_idty; auto).
        eapply Sem.sem_equation_refines in Hsem; eauto.
        eapply In_nth with (d:=xH) in Hinxs as (?&Hlen&Hnth); subst.
        eapply sc_exp_equation in Hsem; rewrite app_nil_r in *; eauto.
        + intros ??? Hin Hvar. eapply sem_clock_refines_iff; try eapply Env.dom_dom_lb; eauto.
          2:eapply Hsem; eauto using sem_var_refines.
          intros ? Hfree.
          eapply wc_env_Is_free_in_clock_In with (vars:=idty env0), InMembers_idty, fst_InMembers in Hfree; eauto.
          eapply in_map_iff. do 2 esplit; eauto. reflexivity.
        + apply NoDupMembers_app_l in Hnd2. apply NoDupMembers_idty; auto.
        + assert (wl_equation G (xs, es)) as Hwl by eauto.
          destruct H1 as (Hwc&_&_).
          eapply Pexp_Pexps; eauto.
          * eapply Forall_forall. intros.
            eapply sc_exp'; eauto.
            apply NoDupMembers_app_l in Hnd2. apply NoDupMembers_idty; auto.
            eapply Forall_forall in Hwc; eauto.
          * intros * Hfree ??? Hin Hvar.
            eapply sem_clock_refines; eauto. eapply Hsc; eauto.
            -- clear - Hin. now eapply in_map_iff; do 2 esplit; eauto.
            -- constructor. repeat esplit; eauto.
               eapply nth_error_nth'; eauto.
            -- eapply sem_var_refines_iff; try eapply Env.dom_dom_lb; eauto.
               eapply in_map_iff. now do 2 esplit; eauto.
          * inv Hwl. congruence.
      - (* reset *)
        eapply in_concat in Hinxs as (?&Hin1&Hin2).
        eapply Forall2_ignore1, Forall_forall in H4 as (?&Hinblk&Hvars); eauto.
        eapply Forall_forall in H; eauto.
        eapply sc_var_inv_unmask; eauto.
        intros k. specialize (H11 k).
        eapply H with (bs:=maskb k r bs); eauto.
        3-6:rewrite Forall_forall in *; try rewrite map_app, map_fst_idcaus; eauto.
        + clear - Hinblk Hnd1.
          unfold idck, idckcaus in *. rewrite 2 map_app, 3 map_map in *.
          eapply nodup_app_map_flat_map; eauto.
        + clear - Hinblk Hnd2.
          rewrite fst_NoDupMembers, map_app, map_fst_idck in *.
          rewrite map_app, app_assoc in Hnd2. eapply NoDup_app_l in Hnd2.
          eapply nodup_app_map_flat_map; eauto.
        + eapply NoDupLocals_incl; eauto.
          eapply incl_app; [eapply incl_appl, incl_refl|eapply incl_appr, incl_map, incl_appl].
          intros ??. eapply in_flat_map; eauto.
        + etransitivity; eauto using incl_concat.
        + eapply Env.dom_map in Hdom; eauto.
        + intros ? Hin Hdep. eapply sc_var_inv_mask; eauto.
          eapply Hsc; eauto. constructor; eapply Exists_exists; eauto.
        + intros ? Hin Hdep. eapply HenvP; eauto.
          2:constructor; eapply Exists_exists; eauto.
          eapply incl_map; eauto. apply incl_map. intros ??; apply in_flat_map; eauto.
      - (* locals *)
        assert (In y (concat xs0)) as Hinxs0 by (rewrite <-H7; auto with datatypes).
        eapply in_concat in Hinxs0 as (?&Hin1&Hin2).
        assert (Env.dom_lb Hl (map fst locs)) as Hdom2.
        { eapply Env.dom_lb_incl with (ys:=concat xs0); [rewrite <-H7; eapply incl_appl, incl_refl|].
          eapply Env.dom_lb_concat.
          rewrite Forall_forall in *. intros.
          eapply Forall2_ignore1, Forall_forall in H3 as (?&Hinblk&Hvars); eauto.
          eapply sem_block_dom_lb; eauto using sem_block_ck'_sem_block.
          eapply NoDupLocals_incl; eauto.
          etransitivity; [eapply incl_concat; eauto|]. rewrite <-H7.
          rewrite Permutation_app_comm, <-app_assoc.
          eapply incl_app; [eapply incl_appl; eauto|solve_incl_app].
        }
        eapply Forall2_ignore1, Forall_forall in H3 as (?&Hinblk&Hvars); eauto.
        eapply Forall_forall in H; eauto.
        assert (Env.refines (EqSt (A:=svalue)) Hi
                              (Env.union Hi (Env.restrict Hl (map fst env0 ++ map fst locs)))) as Href2.
          { intros ?? Hfind. destruct (Env.find x1 (Env.restrict Hl (map fst env0 ++ map fst locs))) eqn:Hfind'.
            - exists s. split; eauto using Env.union_find3'.
              eapply sem_var_det; [now econstructor; try eapply Hfind|].
              eapply H6; eauto.
              + eapply sem_var_restrict_inv. now econstructor; eauto.
              + intros contra. eapply H5; eauto.
                eapply in_or_app, or_introl, Env.dom_use; eauto. econstructor; eauto.
            - exists v. split; try reflexivity.
              eapply Env.union_find2; eauto. }
        assert (sc_var_inv (env0 ++ idckcaus locs)
                           (Env.union Hi (Env.restrict Hl (map fst env0 ++ map fst locs))) bs cy) as Hsc'.
        { assert (Env.refines (EqSt (A:=svalue)) (Env.restrict Hl (map fst (idty env0 ++ idck (idty locs))))
                              (Env.union Hi (Env.restrict Hl (map fst env0 ++ map fst locs)))) as Href1.
          { intros ?? Hfind. exists v. split; try reflexivity.
            rewrite map_app, map_fst_idck, 2 map_fst_idty in Hfind.
            eapply Env.union_find3'; eauto. }
          eapply H; eauto.
          - clear - Hinblk Hnd1. rewrite idckcaus_app, app_assoc in Hnd1.
            unfold idck, idckcaus in *. rewrite 2 map_app, 3 map_map in *.
            eapply nodup_app_map_flat_map; eauto.
          - clear - Hnd2 Hinblk H4 H5.
            rewrite idty_app, <-app_assoc, (Permutation_app_comm _ (idck _)), app_assoc.
            apply NoDupMembers_app; auto.
            + rewrite fst_NoDupMembers, map_app, map_fst_idck in *.
              eapply nodup_app_map_flat_map; eauto.
            + rewrite idty_idckcaus, NoDupMembers_idck, NoDupMembers_idty; auto.
            + intros * Hinm contra. rewrite fst_InMembers, map_app, map_fst_idty, map_fst_idck in Hinm.
              rewrite idty_idckcaus, InMembers_idck, InMembers_idty in contra.
              eapply H5; eauto. rewrite in_app_iff in *. destruct Hinm; auto.
              right. rewrite <-fst_InMembers in *.
              eapply InMembers_anon_in_block; eauto.
          - rewrite Forall_forall in *. eapply NoDupLocals_incl; eauto.
            rewrite map_app, map_fst_idckcaus, <-2 app_assoc, (Permutation_app_comm (map fst locs)).
            eapply incl_appr', incl_appl', incl_map.
            intros ??. eapply in_flat_map; eauto.
          - rewrite map_app, map_fst_idckcaus.
            etransitivity; eauto using incl_concat.
            rewrite <-H7, Permutation_app_comm.
            apply incl_app; [apply incl_appl|apply incl_appr, incl_refl]; eauto.
          - rewrite idty_app. eapply Forall_app; split; eauto.
            + eapply Forall_impl; [|eauto]; intros; simpl in *.
              eapply wc_clock_incl; [|eauto]. solve_incl_app.
            + rewrite idty_idckcaus. rewrite Forall_map in H9. eapply Forall_impl; [|eauto]; eauto.
          - rewrite idty_app, idty_idckcaus. rewrite Forall_forall in *; eauto.
          - rewrite Forall_forall in *.
            assert (NoDupLocals x x0) as Hndl.
            { eapply NoDupLocals_incl; [|eauto].
              etransitivity; [eapply incl_concat; eauto|]. rewrite <-H7.
              rewrite Permutation_app_comm. apply incl_appl'.
              apply incl_appl; auto. }
            eapply sem_block_ck'_refines, sem_block_ck'_restrict; eauto.
          - rewrite map_app, map_fst_idckcaus.
            eapply union_dom_ub_dom_lb_dom; eauto using Env.restrict_dom_ub.
            eapply Env.dom_lb_restrict_dom_lb; [eapply incl_appr, incl_refl|eauto].
          - rewrite idck_app, in_app_iff; auto.
          - intros ? _ Hdep ??? Hin Hv.
            apply in_app_iff in Hin as [Hin|Hin].
            + eapply sem_clock_refines; [eapply Href2|].
              eapply Hsc; eauto.
              * repeat (eapply in_map_iff; do 2 esplit); eauto. reflexivity.
              * rewrite idck_app, idck_idckcaus in Hdep.
                constructor; simpl. eapply Exists_exists; do 2 esplit; eauto.
              * eapply sem_var_refines'; [| |eauto|eauto].
                2:eapply Env.dom_dom_lb; eauto.
                eapply in_map_iff; do 2 esplit; eauto. reflexivity.
            + eapply Forall_forall in H13.
              eapply sem_clock_refines', H13; eauto.
              * eapply Forall_forall in H9; eauto.
                eapply in_map_iff in Hin as ((?&(?&?)&?)&Heq&?); inv Heq.
                repeat (eapply in_map_iff; do 2 esplit); eauto. reflexivity.
              * intros ?? Hin' Hv'. inv Hv'.
                { eapply Env.union_find4' in H1 as [(Hfind1&Hfind2)|Hfind2].
                  - econstructor; eauto.
                    eapply Env.union_find2; eauto using Env.restrict_find_None.
                  - econstructor; eauto.
                    eapply Env.union_find3', Env.restrict_find; eauto.
                    now rewrite fst_InMembers, map_app, map_fst_idck, 2 map_fst_idty in Hin'.
                }
              * eapply sem_var_refines; [|eauto]. intros ?? Hfind.
                { eapply Env.union_find4' in Hfind as [(Hfind1&Hfind2)|Hfind2].
                  - destruct (Env.find x2 Hl) eqn:Hfind3.
                    + assert (v ≡ s).
                      { eapply sem_var_det with (H:=Hi). econstructor; eauto; reflexivity.
                        eapply H6; eauto. econstructor; eauto; reflexivity.
                        intro contra. eapply Env.restrict_find in Hfind3. rewrite Hfind3 in Hfind2; congruence.
                        rewrite in_app_iff, <-2 fst_InMembers; auto. }
                      do 2 esplit; eauto. eapply Env.union_find3'; eauto.
                    + do 2 esplit; try reflexivity.
                      eapply Env.union_find2; eauto.
                  - eapply Env.restrict_find_inv in Hfind2 as (?&?).
                    do 2 esplit; try reflexivity.
                    eapply Env.union_find3'; eauto. }
              * eapply HenvP.
                -- eapply in_map_iff in Hin as ((?&(?&?)&?)&Heq&?); inv Heq.
                   rewrite idcaus_app, map_app, in_app_iff. left.
                   repeat (eapply in_map_iff; do 2 esplit); eauto. reflexivity.
                -- constructor. eapply Exists_exists; eauto.
                   rewrite idck_app, idck_idckcaus in Hdep; eauto.
          - intros * Hin Hdep. apply HenvP.
            eapply incl_map; eauto. apply incl_map, incl_appr. intros ??; apply in_flat_map; eauto.
            constructor. eapply Exists_exists.
            rewrite idck_app, idck_idckcaus in Hdep; eauto.
        }
        intros ??? Hin3 Hv.
        eapply sem_var_refines, Hsc' in Hv; eauto using in_or_app.
        eapply sem_clock_refines_iff; try eapply Env.dom_dom_lb; eauto.
        intros * Hfree. rewrite <-map_fst_idty, <-fst_InMembers.
        eapply wc_clock_is_free_in; [|eauto]. eapply wc_env_var; eauto.
        eapply in_map_iff; do 2 esplit; eauto. reflexivity.
    Qed.

    Fact sem_block_ck'_cons_nIn : forall envP x blk Hi bs,
        ~In x (map snd (idcaus (locals blk))) ->
        sem_block_ck' envP Hi bs blk ->
        sem_block_ck' (x::envP) Hi bs blk.
    Proof.
      induction blk using block_ind2; intros * Hnin Hsem;
        simpl in *; inv Hsem.
      - (* equation *)
        constructor; auto.
      - (* reset *)
        econstructor; eauto.
        intros k. specialize (H6 k).
        rewrite Forall_forall in *; intros. eapply H; eauto.
        contradict Hnin. eapply incl_map; eauto. apply incl_map.
        intros ??. apply in_flat_map; eauto.
      - (* locals *)
        econstructor; eauto.
        + rewrite Forall_forall in *; intros. eapply H; eauto.
          contradict Hnin. eapply incl_map; eauto. apply incl_map, incl_appr.
          intros ??. apply in_flat_map; eauto.
        + constructor; auto.
          intros ??? Hin. exfalso.
          eapply Hnin. rewrite idcaus_app, map_app, in_app_iff. left.
          eapply in_map_iff in Hin as ((?&(?&?)&?)&Heq&?); inv Heq.
          repeat (eapply in_map_iff; do 2 esplit); eauto. reflexivity.
    Qed.

    Lemma sem_block_ck'_cons_In : forall envP blk env xs Hi bs y cy,
        wc_global G ->
        NoDup (map snd (idck (env ++ idckcaus (locals blk)))) ->
        NoDupMembers (idty env ++ idck (anon_in_block blk)) ->
        NoDupLocals (map fst env ++ map fst (anon_in_block blk)) blk ->
        VarsDefined blk xs ->
        incl xs (map fst env) ->
        wc_env (idty env) ->
        wc_block G (idty env) blk ->
        sem_block_ck' envP Hi bs blk ->
        Env.dom Hi (map fst env) ->
        In (y, cy) (idcaus (locals blk)) ->
        (forall cx, In cx (map snd (idck env)) -> depends_on (idck env) cy cx blk -> sc_var_inv env Hi bs cx) ->
        (forall cx, In cx (map snd (idcaus (locals blk))) -> depends_on (idck env) cy cx blk -> In cx envP) ->
        sem_block_ck' (cy::envP) Hi bs blk.
    Proof.
      induction blk as [(xs&es)| |] using block_ind2;
        intros * HwG Hnd1 Hnd2 Hnd3 Hvars Hincl Hwenv Hwc Hsem Hdom Hinenv Hsc HenvP;
        inv Hnd3; inv Hvars; inv Hwc; inv Hsem; simpl in *.
      - (* equation *)
        inv Hinenv.
      - (* reset *)
        econstructor; eauto. intros k. specialize (H11 k).
        eapply Forall2_ignore2 in H4.
        rewrite Forall_forall in *; intros * Hinblk.
        destruct (in_dec ident_eq_dec cy (map snd (idcaus (locals x)))).
        2:eapply sem_block_ck'_cons_nIn; eauto.
        eapply in_map_iff in i as ((?&?)&?&?); subst.
        edestruct H4 as (?&Hinvars&Hvars'); eauto.
        eapply H with (env:=env0); eauto.
        + clear - Hinblk Hnd1.
          unfold idck, idckcaus in *. rewrite 2 map_app, 3 map_map in *.
          eapply nodup_app_map_flat_map; eauto.
        + clear - Hinblk Hnd2.
          rewrite fst_NoDupMembers, map_app, map_fst_idck in *.
          rewrite map_app, app_assoc in Hnd2. eapply NoDup_app_l in Hnd2.
          eapply nodup_app_map_flat_map; eauto.
        + eapply NoDupLocals_incl; eauto.
          eapply incl_app; [eapply incl_appl, incl_refl|eapply incl_appr, incl_map, incl_appl].
          intros ??. eapply in_flat_map; eauto.
        + etransitivity; eauto using incl_concat.
        + eapply Env.dom_map; eauto.
        + intros * Hin Hdep.
          eapply sc_var_inv_mask, Hsc; eauto.
          constructor; simpl. eapply Exists_exists; do 2 esplit; eauto.
        + intros * Hin Hdep. apply HenvP.
          eapply incl_map; eauto. apply incl_map. intros ??; apply in_flat_map; eauto.
          constructor. eapply Exists_exists; do 2 esplit; eauto.
      - (* locals *)
        assert (Env.dom_lb Hl (map fst locs)) as Hdom2.
        { eapply Env.dom_lb_incl with (ys:=concat xs0); [rewrite <-H7; eapply incl_appl, incl_refl|].
          eapply Env.dom_lb_concat.
          rewrite Forall_forall in *. intros.
          eapply Forall2_ignore1, Forall_forall in H3 as (?&Hinblk&Hvars); eauto.
          eapply sem_block_dom_lb; eauto using sem_block_ck'_sem_block.
          eapply NoDupLocals_incl; eauto.
          etransitivity; [eapply incl_concat; eauto|]. rewrite <-H7.
          rewrite Permutation_app_comm, <-app_assoc.
          eapply incl_app; [eapply incl_appl; eauto|solve_incl_app].
        }
        assert (Env.refines (EqSt (A:=svalue)) Hi
                            (Env.union Hi (Env.restrict Hl (map fst env0 ++ map fst locs)))) as Href2.
        { intros ?? Hfind. destruct (Env.find x (Env.restrict Hl (map fst env0 ++ map fst locs))) eqn:Hfind'.
          - exists s. split; eauto using Env.union_find3'.
            eapply sem_var_det; [now econstructor; try eapply Hfind|].
            eapply H6; eauto.
            + eapply sem_var_restrict_inv. now econstructor; eauto.
            + intros contra. eapply H5; eauto.
                eapply in_or_app, or_introl, Env.dom_use; eauto. econstructor; eauto.
          - exists v. split; try reflexivity.
            eapply Env.union_find2; eauto. }
        rewrite idcaus_app, in_app_iff in Hinenv. destruct Hinenv as [Hinenv|Hinenv].
        + (* current locs *)
          econstructor; eauto.
          * rewrite Forall_forall in *; intros.
            eapply sem_block_ck'_cons_nIn; eauto.
            rewrite idckcaus_app, 2 idck_app, 2 map_app in Hnd1. eapply NoDup_app_r in Hnd1.
            eapply NoDup_app_In in Hnd1; eauto.
            2:rewrite idck_idckcaus; eapply in_map_iff; now do 2 esplit; eauto.
            contradict Hnd1. rewrite idck_idckcaus. eapply incl_map; eauto. apply incl_map.
            intros ??. apply in_flat_map; eauto.
          * constructor; auto.
            assert (In y (concat xs0)) as Hinxs0.
            { rewrite <-H7. apply in_app_iff; left. rewrite <-map_fst_idcaus.
              eapply in_map_iff; do 2 esplit; eauto. reflexivity. }
            eapply in_concat in Hinxs0 as (?&Hin1&Hin2).
                        eapply Forall2_ignore1, Forall_forall in H3 as (?&Hinblk&Hvars); eauto.
            eapply Forall_forall in H; eauto.
            assert (Env.refines (EqSt (A:=svalue)) (Env.restrict Hl (map fst (idty env0 ++ idck (idty locs))))
                                (Env.union Hi (Env.restrict Hl (map fst env0 ++ map fst locs)))) as Href1.
            { intros ?? Hfind. exists v. split; try reflexivity.
              rewrite map_app, map_fst_idck, 2 map_fst_idty in Hfind.
              eapply Env.union_find3'; eauto. }
            assert (sc_var_inv (env0 ++ idckcaus locs)
                               (Env.union Hi (Env.restrict Hl (map fst env0 ++ map fst locs))) bs cy) as Hsc'.
            { eapply sc_block with (envP:=envP); eauto.
              - clear - Hinblk Hnd1. rewrite idckcaus_app, app_assoc in Hnd1.
                unfold idck, idckcaus in *. rewrite 2 map_app, 3 map_map in *.
                eapply nodup_app_map_flat_map; eauto.
              - clear - Hnd2 Hinblk H4 H5.
                rewrite idty_app, <-app_assoc, (Permutation_app_comm _ (idck _)), app_assoc.
                apply NoDupMembers_app; auto.
                + rewrite fst_NoDupMembers, map_app, map_fst_idck in *.
                  eapply nodup_app_map_flat_map; eauto.
                + rewrite idty_idckcaus, NoDupMembers_idck, NoDupMembers_idty; auto.
                + intros * Hinm contra. rewrite fst_InMembers, map_app, map_fst_idty, map_fst_idck in Hinm.
                  rewrite idty_idckcaus, InMembers_idck, InMembers_idty in contra.
                  eapply H5; eauto. rewrite in_app_iff in *. destruct Hinm; auto.
                  right. rewrite <-fst_InMembers in *.
                  eapply InMembers_anon_in_block; eauto.
              - rewrite Forall_forall in *. eapply NoDupLocals_incl; eauto.
                rewrite map_app, map_fst_idckcaus, <-2 app_assoc, (Permutation_app_comm (map fst locs)).
                eapply incl_appr', incl_appl', incl_map.
                intros ??. eapply in_flat_map; eauto.
              - rewrite map_app, map_fst_idckcaus.
                etransitivity; eauto using incl_concat.
                rewrite <-H7, Permutation_app_comm.
                apply incl_app; [apply incl_appl|apply incl_appr, incl_refl]; eauto.
              - rewrite idty_app. eapply Forall_app; split; eauto.
                + eapply Forall_impl; [|eauto]; intros; simpl in *.
                  eapply wc_clock_incl; [|eauto]. solve_incl_app.
                + rewrite idty_idckcaus. rewrite Forall_map in H9. eapply Forall_impl; [|eauto]; eauto.
              - rewrite idty_app, idty_idckcaus. rewrite Forall_forall in *; eauto.
              - rewrite Forall_forall in *.
                assert (NoDupLocals x x0) as Hndl.
                { eapply NoDupLocals_incl; [|eauto].
                  etransitivity; [eapply incl_concat; eauto|]. rewrite <-H7.
                  rewrite Permutation_app_comm. apply incl_appl'.
                  apply incl_appl; auto. }
                eapply sem_block_ck'_refines, sem_block_ck'_restrict; eauto.
              - rewrite map_app, map_fst_idckcaus.
                eapply union_dom_ub_dom_lb_dom; eauto using Env.restrict_dom_ub.
                eapply Env.dom_lb_restrict_dom_lb; [eapply incl_appr, incl_refl|eauto].
              - rewrite idck_app, idck_idckcaus, in_app_iff; auto.
              - intros ? _ Hdep ??? Hin Hv.
                apply in_app_iff in Hin as [Hin|Hin].
                + eapply sem_clock_refines; [eapply Href2|].
                  eapply Hsc; eauto.
                  * repeat (eapply in_map_iff; do 2 esplit); eauto. reflexivity.
                  * rewrite idck_app, idck_idckcaus in Hdep.
                    constructor; simpl. eapply Exists_exists; do 2 esplit; eauto.
                  * eapply sem_var_refines'; [| |eauto|eauto].
                    2:eapply Env.dom_dom_lb; eauto.
                    eapply in_map_iff; do 2 esplit; eauto. reflexivity.
                + eapply Forall_forall in H13.
              eapply sem_clock_refines', H13; eauto.
              * eapply Forall_forall in H9; eauto.
                eapply in_map_iff in Hin as ((?&(?&?)&?)&Heq&?); inv Heq.
                repeat (eapply in_map_iff; do 2 esplit); eauto. reflexivity.
              * intros ?? Hin' Hv'. inv Hv'.
                { eapply Env.union_find4' in H1 as [(Hfind1&Hfind2)|Hfind2].
                  - econstructor; eauto.
                    eapply Env.union_find2; eauto using Env.restrict_find_None.
                  - econstructor; eauto.
                    eapply Env.union_find3', Env.restrict_find; eauto.
                    now rewrite fst_InMembers, map_app, map_fst_idck, 2 map_fst_idty in Hin'.
                }
              * eapply sem_var_refines; [|eauto]. intros ?? Hfind.
                { eapply Env.union_find4' in Hfind as [(Hfind1&Hfind2)|Hfind2].
                  - destruct (Env.find x2 Hl) eqn:Hfind3.
                    + assert (v ≡ s).
                      { eapply sem_var_det with (H:=Hi). econstructor; eauto; reflexivity.
                        eapply H6; eauto. econstructor; eauto; reflexivity.
                        intro contra. eapply Env.restrict_find in Hfind3. rewrite Hfind3 in Hfind2; congruence.
                        rewrite in_app_iff, <-2 fst_InMembers; auto. }
                      do 2 esplit; eauto. eapply Env.union_find3'; eauto.
                    + do 2 esplit; try reflexivity.
                      eapply Env.union_find2; eauto.
                  - eapply Env.restrict_find_inv in Hfind2 as (?&?).
                    do 2 esplit; try reflexivity.
                    eapply Env.union_find3'; eauto. }
              * eapply HenvP.
                -- eapply in_map_iff in Hin as ((?&(?&?)&?)&Heq&?); inv Heq.
                   rewrite idcaus_app, map_app, in_app_iff. left.
                   repeat (eapply in_map_iff; do 2 esplit); eauto. reflexivity.
                -- constructor. eapply Exists_exists; eauto.
                   rewrite idck_app, idck_idckcaus in Hdep; eauto.
              - intros * Hin Hdep. apply HenvP.
                eapply incl_map; eauto. apply incl_map, incl_appr. intros ??; apply in_flat_map; eauto.
                constructor. eapply Exists_exists; do 2 esplit; eauto.
                now rewrite idck_app, idck_idckcaus in Hdep.
            }
            intros ??? Hin3 Hv.
            assert (Env.refines (@EqSt _) (Env.union Hi (Env.restrict Hl (map fst env0 ++ map fst locs)))
                                (Env.union Hi Hl)) as Href.
            { intros ?? Hfind. eapply Env.union_find4' in Hfind as [(Hfind1&Hfind2)|Hfind2].
              - destruct (Env.find x2 Hl) eqn:Hfind3.
                + assert (v ≡ s).
                  { eapply sem_var_det with (H:=Hi). econstructor; eauto; reflexivity.
                    eapply H6; eauto. econstructor; eauto; reflexivity.
                    intro contra. eapply Env.restrict_find in Hfind3. rewrite Hfind3 in Hfind2; congruence.
                    rewrite in_app_iff, <-2 fst_InMembers; auto. }
                  do 2 esplit; eauto. eapply Env.union_find3'; eauto.
                + do 2 esplit; try reflexivity.
                  eapply Env.union_find2; eauto.
              - eapply Env.restrict_find_inv in Hfind2 as (?&?).
                do 2 esplit; try reflexivity.
                eapply Env.union_find3'; eauto. }
            eapply sem_clock_refines, Hsc'; eauto using in_or_app.
            eapply sem_var_refines'; [| |eauto|eauto].
            -- eapply in_map_iff. do 2 esplit; eauto. instantiate (1:=fst). reflexivity.
            -- eapply Env.union_dom_lb2, Env.dom_lb_restrict_dom_lb; eauto.
               1,2:rewrite map_fst_idckcaus; auto. apply incl_appr, incl_refl.
        + (* deeper *)
          eapply Forall2_ignore2 in H3; eauto.
          assert (Env.refines (@EqSt _) Hl (Env.union Hi (Env.restrict Hl (map fst env0 ++ map fst locs)))) as Href1.
          { intros ?? Hfind. destruct (in_dec ident_eq_dec x (map fst locs)).
            - do 2 esplit; try reflexivity.
              eapply Env.union_find3', Env.restrict_find; eauto using in_or_app.
            - rewrite <-fst_InMembers in n. eapply H6 in n. 2:(econstructor; eauto; reflexivity).
              inv n.
              destruct (Env.find x (Env.restrict Hl (map fst env0 ++ map fst locs))) eqn:Hfind2.
              + assert (Hfind2':=Hfind2). eapply Env.restrict_find_inv in Hfind2 as (?&Hfind2).
                rewrite Hfind2 in Hfind; inv Hfind.
                do 2 eexists; [|eauto using Env.union_find3']. reflexivity.
              + do 2 eexists; eauto. eapply Env.union_find2; eauto. }
          eapply Scklocal with (Hl:=(Env.union Hi (Env.restrict Hl (map fst env0 ++ map fst locs)))); eauto.
          * intros * Hvar Hnin. inv Hvar.
            { eapply Env.union_find4' in H1 as [(Hfind1&Hfind2)|Hfind2].
              - econstructor; eauto.
              - eapply Env.restrict_find_inv in Hfind2 as (?&Hfind2).
                eapply H6; eauto. econstructor; eauto. }
          * rewrite Forall_forall in *; intros * Hinblk.
            destruct (in_dec ident_eq_dec cy (map snd (idcaus (locals x)))).
            2:eapply sem_block_ck'_cons_nIn; eauto.
            { edestruct H3 as (?&Hinvars&Hvars'); eauto.
              eapply in_map_iff in i as ((?&?)&?&?); subst.
              eapply H with (env:=env0++idckcaus locs); eauto.
              - clear - Hinblk Hnd1. rewrite idckcaus_app, app_assoc in Hnd1.
                unfold idck, idckcaus in *. rewrite 2 map_app, 3 map_map in *.
                eapply nodup_app_map_flat_map; eauto.
              - clear - Hnd2 Hinblk H4 H5.
                rewrite idty_app, <-app_assoc, (Permutation_app_comm _ (idck _)), app_assoc.
                apply NoDupMembers_app; auto.
                + rewrite fst_NoDupMembers, map_app, map_fst_idck in *.
                  eapply nodup_app_map_flat_map; eauto.
                + rewrite idty_idckcaus, NoDupMembers_idck, NoDupMembers_idty; auto.
                + intros * Hinm contra. rewrite fst_InMembers, map_app, map_fst_idty, map_fst_idck in Hinm.
                  rewrite idty_idckcaus, InMembers_idck, InMembers_idty in contra.
                  eapply H5; eauto. rewrite in_app_iff in *. destruct Hinm; auto.
                  right. rewrite <-fst_InMembers in *.
                  eapply InMembers_anon_in_block; eauto.
              - eapply NoDupLocals_incl; eauto.
                rewrite map_app, map_fst_idckcaus, <-2 app_assoc, (Permutation_app_comm (map fst locs)).
                eapply incl_appr', incl_appl', incl_map.
                intros ??. eapply in_flat_map; eauto.
              - rewrite map_app, map_fst_idckcaus.
                etransitivity; eauto using incl_concat.
                rewrite <-H7, Permutation_app_comm.
                apply incl_app; [apply incl_appl|apply incl_appr, incl_refl]; eauto.
              - rewrite idty_app. eapply Forall_app; split; eauto.
                + eapply Forall_impl; [|eauto]; intros; simpl in *.
                  eapply wc_clock_incl; [|eauto]. solve_incl_app.
                + rewrite idty_idckcaus. rewrite Forall_forall; intros. eapply H9; eauto.
                  eapply in_map_iff; do 2 esplit; eauto.
              - rewrite idty_app, idty_idckcaus; eauto.
              - assert (NoDupLocals x0 x) as Hndl.
                { eapply NoDupLocals_incl; [|eauto].
                  etransitivity; [eapply incl_concat; eauto|]. rewrite <-H7.
                  rewrite Permutation_app_comm. apply incl_appl'.
                  apply incl_appl; auto. }
                eapply sem_block_ck'_refines, sem_block_ck'_restrict; eauto.
                intros ?? Hfind. do 2 esplit; try reflexivity.
                rewrite map_app, map_fst_idck, 2 map_fst_idty in Hfind.
                eapply Env.union_find3'; eauto.
              - rewrite map_app, map_fst_idckcaus.
                eapply union_dom_ub_dom_lb_dom; eauto using Env.restrict_dom_ub.
                eapply Env.dom_lb_restrict_dom_lb; [eapply incl_appr, incl_refl|eauto].
              - intros ? _ Hdep ??? Hin Hv.
                apply in_app_iff in Hin as [Hin|Hin].
                + eapply sem_clock_refines; [eapply Href2|].
                  eapply Hsc; eauto.
                  * repeat (eapply in_map_iff; do 2 esplit); eauto. reflexivity.
                  * rewrite idck_app, idck_idckcaus in Hdep.
                    constructor; simpl. eapply Exists_exists; do 2 esplit; eauto.
                  * eapply sem_var_refines'; [| |eauto|eauto].
                    2:eapply Env.dom_dom_lb; eauto.
                    eapply in_map_iff; do 2 esplit; eauto. reflexivity.
                + eapply sem_clock_refines', H13; eauto.
              * eapply H9; eauto.
                eapply in_map_iff in Hin as ((?&(?&?)&?)&Heq&?); inv Heq.
                repeat (eapply in_map_iff; do 2 esplit); eauto. reflexivity.
              * intros ?? Hin' Hv'. inv Hv'.
                { eapply Env.union_find4' in H10 as [(Hfind1&Hfind2)|Hfind2].
                  - econstructor; eauto.
                    eapply Env.union_find2; eauto using Env.restrict_find_None.
                  - econstructor; eauto.
                    eapply Env.union_find3', Env.restrict_find; eauto.
                    now rewrite fst_InMembers, map_app, map_fst_idck, 2 map_fst_idty in Hin'.
                }
              * eapply HenvP.
                -- eapply in_map_iff in Hin as ((?&(?&?)&?)&Heq&?); inv Heq.
                   rewrite idcaus_app, map_app, in_app_iff. left.
                   repeat (eapply in_map_iff; do 2 esplit); eauto. reflexivity.
                -- constructor. eapply Exists_exists; eauto.
                   rewrite idck_app, idck_idckcaus in Hdep; eauto.
              * eapply sem_var_refines; [|eauto]. intros ?? Hfind.
                { eapply Env.union_find4' in Hfind as [(Hfind1&Hfind2)|Hfind2].
                  - destruct (Env.find x2 Hl) eqn:Hfind3.
                    + assert (v ≡ s).
                      { eapply sem_var_det with (H:=Hi). econstructor; eauto; reflexivity.
                        eapply H6; eauto. econstructor; eauto; reflexivity.
                        intro contra. eapply Env.restrict_find in Hfind3. rewrite Hfind3 in Hfind2; congruence.
                        rewrite in_app_iff, <-2 fst_InMembers; auto. }
                      do 2 esplit; eauto. eapply Env.union_find3'; eauto.
                    + do 2 esplit; try reflexivity.
                      eapply Env.union_find2; eauto.
                  - eapply Env.restrict_find_inv in Hfind2 as (?&?).
                    do 2 esplit; try reflexivity. eapply Env.union_find3'; eauto.
                }
              - intros * Hin Hdep. apply HenvP.
                eapply incl_map; eauto. apply incl_map, incl_appr. intros ??; apply in_flat_map; eauto.
                constructor. eapply Exists_exists; do 2 esplit; eauto.
                now rewrite idck_app, idck_idckcaus in Hdep.
            }
            edestruct H3 as (?&?&Hvars); eauto.
            assert (NoDupLocals x0 x) as Hndl.
            { eapply NoDupLocals_incl; [|eauto].
              etransitivity; [eapply incl_concat; eauto|]. rewrite <-H7.
              rewrite Permutation_app_comm. apply incl_appl'.
              apply incl_appl; auto. }
            eapply sem_block_ck'_refines, sem_block_ck'_restrict; eauto.
            intros ?? Hfind. do 2 esplit; try reflexivity.
            rewrite map_app, map_fst_idck, 2 map_fst_idty in Hfind.
            eapply Env.union_find3'; eauto.
          * assert (Env.refines (@EqSt _) (Env.union Hi Hl)
                                (Env.union Hi (Env.union Hi (Env.restrict Hl (map fst env0 ++ map fst locs))))).
            { intros ?? Hfind. eapply Env.union_find4' in Hfind as [(Hfind1&Hfind2)|Hfind2].
              - eapply Href2 in Hfind1 as (?&?&?).
                do 2 esplit; eauto. eapply Env.union_find3'; eauto.
              - eapply Href1 in Hfind2 as (?&?&?).
                do 2 esplit; eauto. eapply Env.union_find3'; eauto. }
            { constructor; auto.
              - intros ??? Hin. exfalso.
                eapply in_map_iff in Hin as ((?&(?&?)&?)&Heq&?); inv Heq.
                rewrite idck_app, map_app, idck_idckcaus, idcaus_app, map_app in Hnd1.
                eapply NoDup_app_r, NoDup_app_In in Hnd1; eauto. eapply Hnd1.
                1,2:eapply in_map_iff; do 2 esplit. 1,2:eauto.
                2:eapply in_map_iff; do 2 esplit; eauto. reflexivity.
              - eapply Forall_impl; [|eauto]; intros ? Hsc' ??? Hin Hv.
                eapply sem_clock_refines, Hsc'; eauto.
                eapply sem_var_refines_iff; [eauto| | |eauto]. eapply Env.union_dom_lb2; eauto.
                rewrite <-map_fst_idckcaus. eapply in_map_iff; do 2 esplit; eauto. reflexivity.
            }
    Qed.

    Lemma sem_node_sc_vars :
      forall n H b,
        wc_global G ->
        wc_node G n ->
        node_causal n ->
        Env.dom H (map fst (n_in n ++ n_out n)) ->
        Forall (sc_var_inv (idckcaus (n_in n ++ n_out n)) H b) (map snd (idcaus (n_in n))) ->
        Sem.sem_block G H b (n_block n) ->
        sc_vars (idty (idckcaus (n_in n ++ n_out n))) H b /\
        sem_block_ck' (map snd (idcaus (n_in n ++ n_out n ++ locals (n_block n)))) H b (n_block n).
    Proof.
      intros * HwcG Hwcn Hcau Hdom Hins Hsem.
      assert (Forall (sc_var_inv (idckcaus (n_in n ++ n_out n)) H b) (map snd (idcaus (n_in n ++ n_out n ++ locals (n_block n)))) /\
              sem_block_ck' (map snd (idcaus (n_in n ++ n_out n ++ locals (n_block n)))) H b (n_block n)) as (?&?).
      2:{ split; auto.
          eapply sc_var_inv_sc_vars.
          - eapply Forall_forall; intros * Hin. rewrite map_fst_idckcaus in Hin.
            eapply Env.dom_use in Hin; eauto. inv Hin.
            do 2 esplit; eauto. reflexivity.
          - eapply Forall_incl; eauto.
            rewrite idck_idckcaus.
            repeat rewrite idcaus_app. solve_incl_app. }
      eapply node_causal_ind2; eauto.
      - intros ?? Hperm (Hvars&Hlocs). split. rewrite <-Hperm; auto.
        eapply sem_block_ck'_Perm; eauto.
      - split; auto. apply sem_block_sem_block_ck'; auto.
      - intros ?? Hin (Hvars&Hlocs) Hdep.
        repeat rewrite idcaus_app, map_app, in_app_iff in Hin.
        destruct Hcau as (Hnd&_). rewrite app_assoc, idcaus_app, map_app in Hnd.
        destruct Hin as [Hin|[Hin|Hin]]; (split; [constructor; auto|]).
        + eapply Forall_forall in Hins; eauto.
        + eapply sem_block_ck'_cons_nIn; eauto.
          eapply NoDup_app_In in Hnd; eauto. rewrite idcaus_app, map_app, in_app_iff; auto.
        + pose proof (n_defd n) as (?&Hdef&Hperm).
          eapply in_map_iff in Hin as ((?&?)&?&Hin); subst.
          eapply sc_block; eauto.
          * rewrite idck_app, 2 idck_idckcaus, map_app; auto.
          * rewrite idty_idckcaus, <-idck_app. apply NoDupMembers_idck, n_nodup.
          * rewrite map_fst_idckcaus. apply n_nodup.
          * rewrite Hperm, map_fst_idckcaus. solve_incl_app.
          * rewrite idty_idckcaus. eapply Hwcn.
          * rewrite idty_idckcaus. eapply Hwcn.
          * now rewrite map_fst_idckcaus.
          * rewrite Hperm, <-map_fst_idcaus. eapply in_map_iff; do 2 esplit; eauto.
          * simpl. rewrite idck_idckcaus, idcaus_app, in_app_iff; auto.
          * intros ?? Hdep'. rewrite idck_idckcaus in Hdep'.
            eapply Forall_forall in Hvars; eauto.
          * intros ?? Hdep'. rewrite idck_idckcaus in Hdep'; eauto.
        + eapply sem_block_ck'_cons_nIn; eauto.
          eapply NoDup_app_In in Hnd; eauto. rewrite idcaus_app, map_app, in_app_iff; auto.
        + intros ??? Hin'. exfalso.
          eapply NoDup_app_In in Hnd; eauto.
          eapply in_map_iff in Hin' as ((?&(?&?)&?)&Heq&Hin'); inv Heq.
          repeat (eapply in_map_iff; do 2 esplit); eauto. reflexivity.
        + pose proof (n_defd n) as (?&Hdef&Hperm).
          eapply in_map_iff in Hin as ((?&?)&?&Hin); subst.
          eapply sem_block_ck'_cons_In with (env:=idckcaus (n_in n ++ n_out n)); eauto.
          * rewrite idck_app, 2 idck_idckcaus, map_app; auto.
          * rewrite idty_idckcaus, <-idck_app. apply NoDupMembers_idck, n_nodup.
          * rewrite map_fst_idckcaus. apply n_nodup.
          * rewrite Hperm, map_fst_idckcaus. solve_incl_app.
          * rewrite idty_idckcaus. eapply Hwcn.
          * rewrite idty_idckcaus. eapply Hwcn.
          * now rewrite map_fst_idckcaus.
          * intros ?? Hdep'. rewrite idck_idckcaus in Hdep'.
            eapply Forall_forall in Hvars; eauto.
          * intros ?? Hdep'. rewrite idck_idckcaus in Hdep'; eauto.
    Qed.

    Lemma sem_clocks_det' : forall H H' b ins vins ss,
        wc_env (idck (idty ins)) ->
        Forall2 (sem_var H) (idents ins) vins ->
        Forall2 (sem_var H') (idents ins) vins ->
        Forall2 (fun xc => sem_clock H b (snd xc)) (idck (idty ins)) ss ->
        Forall2 (fun xs => sem_clock H' b (snd xs)) (idck (idty ins)) ss.
    Proof.
      intros * Hwc Hi1 Hi2 Hck.
      eapply sem_clocks_det in Hck; eauto.
      rewrite idty_app, idck_app.
      apply Forall_app; split; eapply Forall_impl; eauto; intros [? ?] ?.
      1,2:eapply wc_clock_incl; eauto.
      1,2:apply incl_appl; reflexivity.
    Qed.

    Fact sem_var_In : forall H x vs,
        sem_var H x vs ->
        Env.In x H.
    Proof.
      intros * Hv. inv Hv.
      econstructor; eauto.
    Qed.

    Corollary sem_vars_In : forall H xs vs,
        Forall2 (sem_var H) xs vs ->
        Forall (fun v => Env.In v H) xs.
    Proof.
      intros * Hvs.
      induction Hvs; constructor; eauto using sem_var_In.
    Qed.

    Lemma sem_node_restrict {prefs2} : forall (n : @node PSyn prefs2) H b xs ys,
        wc_block G (idck (idty (n_in n ++ n_out n))) (n_block n) ->
        Forall2 (sem_var H) (idents (n_in n)) xs ->
        Forall2 (sem_var H) (idents (n_out n)) ys ->
        Sem.sem_block G H b (n_block n) ->
        let H' := Env.restrict H (idents (n_in n ++ n_out n)) in
        Env.dom H' (idents (n_in n ++ n_out n)) /\
        Forall2 (sem_var H') (idents (n_in n)) xs /\
        Forall2 (sem_var H') (idents (n_out n)) ys /\
        Sem.sem_block G H' b (n_block n).
    Proof with eauto.
      intros * Hwc Hins Houts Heqs.
      remember (Env.restrict _ _) as H'; simpl.
      repeat split.
      - subst. eapply Env.dom_lb_restrict_dom.
        apply Env.dom_lb_intro. intros x Hin.
        unfold idents in *.
        repeat rewrite map_app in Hin. repeat rewrite in_app_iff in Hin. destruct Hin as [Hin|Hin].
        + apply sem_vars_In in Hins. rewrite Forall_forall in Hins...
        + apply sem_vars_In in Houts. rewrite Forall_forall in Houts...
      - eapply Forall2_impl_In; [|eauto]; intros.
        unfold idents in H0. apply in_map_iff in H0 as ((?&?&?)&?&?); simpl in *; subst.
        eapply sem_var_restrict; eauto.
        eapply in_map_iff; do 2 esplit; eauto using in_or_app. reflexivity.
      - eapply Forall2_impl_In; [|eauto]; intros.
        unfold idents in H0. apply in_map_iff in H0 as ((?&?&?)&?&?); simpl in *; subst.
        eapply sem_var_restrict; eauto.
        eapply in_map_iff; do 2 esplit; eauto using in_or_app. reflexivity.
      - subst. eapply Sem.sem_block_restrict in Heqs; eauto.
        eapply wc_block_wx_block in Hwc.
        rewrite map_fst_idck, map_fst_idty in Hwc. assumption.
    Qed.

    Lemma sc_var_inv_intro {prefs2} : forall (n : @node PSyn prefs2) H xs,
        node_causal n ->
        Forall2 (sem_var H) (idents (n_in n)) xs ->
        Forall2 (fun xc => sem_clock H (clocks_of xs) (snd xc)) (idck (idty (n_in n))) (map abstract_clock xs) ->
        Forall (sc_var_inv (idckcaus (n_in n ++ n_out n)) H (clocks_of xs)) (map snd (idcaus (n_in n))).
    Proof.
      intros * (Hnd&_) Hvar Hclock.
      unfold idents, idck, idty, idcaus in *.
      rewrite Forall2_map_1 in Hvar. rewrite 2 Forall2_map_1, Forall2_map_2 in Hclock.
      rewrite Forall_map, Forall_map.
      eapply Forall2_Forall2 in Hclock; [|eapply Hvar]. eapply Forall2_ignore2 in Hclock.
      clear - Hnd Hclock.
      eapply Forall_impl_In; [|eauto].
      intros (?&(?&?)&?) ? (?&?&?&?) ??? Hin Hv; simpl in *.
      eapply in_map_iff in Hin as ((?&(?&?)&?)&Heq&Hin); inv Heq.
      rewrite in_app_iff in Hin. destruct Hin as [Hin|Hin].
      2:{ exfalso. rewrite 4 map_app in Hnd. eapply NoDup_app_In in Hnd.
          eapply Hnd, in_app_iff. left.
          1,2:(repeat (eapply in_map_iff; do 2 esplit)). 2,3,5,6:eauto. 1,2:eauto.
      }
      rewrite 4 map_app in Hnd. eapply NoDup_app_l, NoDup_snd_det in Hnd.
      2:(eapply in_map_iff; do 2 esplit; try eapply H0); eauto.
      2:(eapply in_map_iff; do 2 esplit; try eapply Hin); eauto. subst.
      eapply sem_var_det in H2; eauto. rewrite H2.
      specialize (node_NoDup n) as Hnd. apply fst_NoDupMembers in Hnd.
      eapply NoDupMembers_det in Hnd; auto.
      2:eapply in_or_app, or_introl, H0. 2:eapply in_or_app, or_introl, Hin.
      inv Hnd; auto.
    Qed.

    Fact wc_exp_Is_free_left : forall env e x k,
        wc_exp G (idty env) e ->
        Is_free_left (idck env) x k e ->
        In x (map snd (idck env)).
    Proof.
      Local Hint Resolve In_InMembers.
      Local Ltac solve_forall_exists H1 H2 H3 :=
        try eapply Is_free_left_list_Exists in H3; try destruct H3 as (?&H3);
        eapply Forall_Forall in H1; [|eapply H2];
        eapply Forall_Exists in H1; [|eapply H3];
        eapply Exists_exists in H1 as (?&?&(?&?)&?); eauto.
      induction e using exp_ind2; intros * Hwc Hfree;
        inv Hwc; inv Hfree; eauto.
      - (* var *) eapply in_map_iff; now do 2 esplit; eauto.
      - (* var *) eapply in_map_iff; now do 2 esplit; eauto.
      - (* binop *) destruct H1; eauto.
      - (* fby *)
        solve_forall_exists H H4 H3.
      - (* arrow *)
        destruct H3 as [Hex|Hex]; eauto.
        solve_forall_exists H H4 Hex. solve_forall_exists H0 H5 Hex.
      - (* when *)
        destruct H2 as [[? Hex]|Hex]; subst; eauto.
        eapply in_map_iff; now do 2 esplit; eauto.
        solve_forall_exists H H5 Hex.
      - (* merge *)
        destruct H2 as [[? Hex]|Hex]; subst; eauto.
        eapply in_map_iff; now do 2 esplit; eauto.
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
    Lemma sc_exp_anon : forall (env : list (ident * (clock * ident))) H b e vs,
        wc_global G ->
        NoDupMembers env ->
        NoDup (map snd (idck env)) ->
        sc_vars (idty env) H b ->

        wc_exp G (idty env) e ->
        Sem.sem_exp G H b e vs ->
        anon_sem_exp G H b e ->
        Forall2 (sem_clock H b) (clockof e) (map abstract_clock vs).
    Proof.
      intros * HwcG Hnd1 Hnd2 Hinv Hwc Hsem Hanon.
      eapply sc_vars_sc_var_inv in Hinv; eauto.
      assert (forall k, k < numstreams e -> sc_exp_inv (idty env0) H b e k); intros.
      eapply exp_causal_ind
             with (P_exp:=sc_exp_inv _ H b); eauto; intros.
      - apply sc_exp_const.
      - apply sc_exp_enum.
      - eapply sc_exp_var; eauto.
      - apply sc_exp_unop; auto.
      - apply sc_exp_binop; auto.
      - apply sc_exp_fby; auto.
      - apply sc_exp_arrow; auto.
      - eapply sc_exp_when; eauto.
      - eapply sc_exp_merge; eauto.
      - apply sc_exp_case; auto.
      - eapply sc_exp_app; eauto.
      - eapply wc_exp_wx_exp in Hwc. rewrite map_fst_idty in Hwc. now rewrite map_fst_idck.
      - intros ? Hcau.
        eapply Forall_forall in Hinv; eauto.
        eapply wc_exp_Is_free_left; eauto.
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

    Corollary sc_exps_anon : forall (env : list (ident * (clock * ident))) H b es vss,
        wc_global G ->
        NoDupMembers env ->
        NoDup (map snd (idck env)) ->
        sc_vars (idty env) H b ->

        Forall (wc_exp G (idty env)) es ->
        Forall2 (Sem.sem_exp G H b) es vss ->
        Forall (anon_sem_exp G H b) es ->
        Forall2 (sem_clock H b) (clocksof es) (map abstract_clock (concat vss)).
    Proof.
      intros * HwcG Hnd1 Hnd2 Hsc Hwc Hsem Hanon.
      unfold clocksof.
      rewrite Forall2_map_2, flat_map_concat_map.
      apply Forall2_concat. rewrite Forall2_map_1.
      eapply Forall2_impl_In; [|eauto]; intros.
      eapply sc_exp_anon in H2; eauto. 2,3:eapply Forall_forall; eauto.
      rewrite Forall2_map_2 in H2; eauto.
    Qed.
  End sc_inv.

  Lemma sc_vars_mask : forall env H b r k,
      sc_vars env H b ->
      sc_vars env (mask_hist k r H) (maskb k r b).
  Proof.
    intros * Hinv.
    eapply Forall_impl; [|eauto]. intros (?&?) (?&Hvar&Hck).
    eapply sem_var_mask in Hvar. eapply sem_clock_mask in Hck.
    exists (maskv k r x). split; eauto. rewrite ac_mask; eauto.
  Qed.

  Lemma sc_vars_unmask : forall env H b r,
      (forall k, sc_vars env (mask_hist k r H) (maskb k r b)) ->
      sc_vars env H b.
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

  Lemma sc_vars_slower_hist : forall env H b,
      sc_vars env H b ->
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
    Context {PSyn : block -> Prop}.
    Context {prefs : PS.t}.
    Variable (G : @global PSyn prefs).

    Hypothesis HwcG : wc_global G.

    Hypothesis Hdet : det_nodes G.

    Hypothesis Hnode : forall f ins outs,
        sem_node G f ins outs ->
        sem_clock_inputs G f ins ->
        sem_node_ck G f ins outs.

    Lemma sem_exp_anon_sem_exp_ck : forall (env : list (ident * (clock * ident))) H bs e vs,
        NoDupMembers env ->
        NoDup (map snd (idck env)) ->
        sc_vars (idty env) H bs ->
        wc_exp G (idty env) e ->
        Sem.sem_exp G H bs e vs ->
        anon_sem_exp G H bs e ->
        sem_exp_ck G H bs e vs.
    Proof.
      induction e using exp_ind2; intros * Hnd1 Hnd2 Hsc Hwc Hsem Hanon;
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
        + eapply sc_exps_anon with (env:=env0); eauto.
      - (* ck_app *)
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

    Corollary sem_equation_anon_sem_equation_ck : forall (env : list (ident * (clock * ident))) H bs equ,
        NoDupMembers env ->
        NoDup (map snd (idck env)) ->
        sc_vars (idty env) H bs ->
        wc_equation G (idty env) equ ->
        Sem.sem_equation G H bs equ ->
        anon_sem_equation G H bs equ ->
        sem_equation_ck G H bs equ.
    Proof.
      intros * Hnd1 Hnd2 Hsc Hwc Hsem Hanon.
      inv Hsem. inv Hwc.
      econstructor; eauto.
      eapply Forall2_impl_In; [|eauto]; intros.
      eapply sem_exp_anon_sem_exp_ck; eauto. 1,2:eapply Forall_forall; eauto.
    Qed.

    Lemma sc_vars_fresh_in : forall H bs e vs,
        sem_exp_ck G H bs e vs ->
        sc_vars (idck (fresh_in e)) H bs.
    Proof.
      unfold sc_vars, idck.
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

    Corollary sc_vars_anon_in : forall H bs e vs,
        sem_exp_ck G H bs e vs ->
        sc_vars (idck (anon_in e)) H bs.
    Proof.
      unfold sc_vars, idck.
      intros * Hsem.
      destruct e. 1-10:eapply sc_vars_fresh_in; eauto.
      inv Hsem.
      simpl. rewrite Forall_map, Forall_app.
      unfold fresh_ins. repeat rewrite flat_map_concat_map.
      split; apply Forall_concat, Forall_map, Forall_forall; intros.
      - eapply Forall2_ignore2, Forall_forall in H5 as (?&?&Hsem); eauto.
        eapply sc_vars_fresh_in in Hsem; eauto.
        unfold sc_vars, idck in *. now rewrite Forall_map in Hsem.
      - eapply Forall2_ignore2, Forall_forall in H8 as (?&?&Hsem); eauto.
        eapply sc_vars_fresh_in in Hsem; eauto.
        unfold sc_vars, idck in *. now rewrite Forall_map in Hsem.
    Qed.

    Corollary sc_vars_anon_in_eq : forall H bs equ,
        sem_equation_ck G H bs equ ->
        sc_vars (idck (anon_in_eq equ)) H bs.
    Proof.
      intros * Hsem. inv Hsem.
      unfold sc_vars, idck, anon_in_eq, anon_ins.
      rewrite flat_map_concat_map.
      apply Forall_map, Forall_concat, Forall_map.
      eapply Forall_forall; intros.
      eapply Forall2_ignore2, Forall_forall in H1 as (?&?&Hsem); eauto.
      eapply sc_vars_anon_in in Hsem.
      unfold sc_vars, idck in *. now rewrite Forall_map in Hsem.
    Qed.

    Lemma sc_vars_local_anon_in_block : forall blk H bs,
        NoDupLocals (map fst (local_anon_in_block blk)) blk ->
        sem_block_ck G H bs blk ->
        sc_vars (idck (local_anon_in_block blk)) H bs.
    Proof.
      unfold sc_vars.
      induction blk using block_ind2; intros * Hnd Hsem;
        inv Hnd; inv Hsem; simpl.
      - (* equation *)
        eapply sc_vars_anon_in_eq; eauto.
      - (* reset *)
        rewrite idck_app, Forall_app; split.
        + eapply sc_vars_unmask; intros k. specialize (H9 k).
          unfold sc_vars, idck.
          rewrite Forall_map, flat_map_concat_map.
          apply Forall_concat, Forall_map.
          eapply Forall_impl_In; [|eapply H]; intros; simpl in *.
          setoid_rewrite Forall_map in H2. eapply Forall_impl; [|eapply H2].
          * intros (?&?&?) ?; eauto.
          * rewrite Forall_forall in *; eauto.
            eapply NoDupLocals_incl; eauto. rewrite map_app.
            apply incl_appl, incl_map. intros ??. eapply in_flat_map; eauto.
          * rewrite Forall_forall in *; eauto.
        + eapply sc_vars_fresh_in in H5; eauto.
      - (* local *)
        constructor.
    Qed.

    Corollary sc_vars_local_anon_in_blocks : forall H bs blks,
        Forall (NoDupLocals (map fst (flat_map local_anon_in_block blks))) blks ->
        Forall (sem_block_ck G H bs) blks ->
        sc_vars (idck (flat_map local_anon_in_block blks)) H bs.
    Proof.
      intros * Hnd Hsem.
      rewrite flat_map_concat_map.
      eapply Forall_map, Forall_concat, Forall_map.
      rewrite Forall_forall in *; intros ? Hin.
      eapply sc_vars_local_anon_in_block, Forall_map in Hsem; eauto.
      eapply NoDupLocals_incl; [|eauto]. apply incl_map.
      intros ??. apply in_flat_map; eauto.
    Qed.

    Hint Resolve Env.union_refines2 Env.union_dom' Env.adds_opt'_refines Env.adds_opt'_dom
         EqStrel EqStrel_Reflexive clocked_app_refines.

    Fact sem_blocks_sem_blocks_ck : forall envP (env: list (ident * (clock * ident))) H bs blks xs,
      Forall
        (fun blk => forall xs (env: list (ident * (clock * ident))) H bs,
             NoDupMembers (idty env ++ idck (anon_in_block blk)) ->
             NoDup (map snd (idck (env ++ idckcaus (locals blk)))) ->
             NoDupLocals (map fst env ++ map fst (anon_in_block blk)) blk ->
             VarsDefined blk xs ->
             incl xs (map fst env) ->
             incl (map snd (idck (env ++ idckcaus (locals blk)))) envP ->
             Env.dom H (map fst env) ->
             sc_vars (idty env) H bs ->
             wc_block G (idty env) blk ->
             sem_block_ck' G envP H bs blk ->
             exists H',
               Env.refines (EqSt (A:=svalue)) H H' /\
               Env.dom H' (map fst env ++ map fst (local_anon_in_block blk)) /\
               sem_block_ck G H' bs blk) blks ->
      NoDupMembers (idty env ++ idck (flat_map anon_in_block blks)) ->
      NoDup (map snd (idck (env ++ idckcaus (flat_map locals blks)))) ->
      Forall (NoDupLocals (map fst env ++ map fst (flat_map anon_in_block blks))) blks ->
      Forall2 VarsDefined blks xs ->
      incl (concat xs) (map fst env) ->
      incl (map snd (idck (env ++ idckcaus (flat_map locals blks)))) envP ->
      Env.dom H (map fst env) ->
      sc_vars (idty env) H bs ->
      Forall (wc_block G (idty env)) blks ->
      Forall (sem_block_ck' G envP H bs) blks ->
      exists H',
        Env.refines (@EqSt _) H H' /\
        Env.dom H' (map fst env ++ map fst (flat_map local_anon_in_block blks)) /\
        Forall (sem_block_ck G H' bs) blks.
    Proof.
      induction blks; intros * Hf Hnd1 Hnd2 Hnd3 Hvars Hincl HenvP Hdom Hsc Hwc Hsem;
        inv Hnd3; inv Hvars; inv Hwc; inv Hsem; inv Hf; simpl in *.
      - simpl_ndup Hnd. exists H; auto.
      - eapply incl_app' in Hincl as (Hincl1&Hincl2).
        rewrite idckcaus_app, 2 idck_app, 2 map_app in HenvP.
        eapply IHblks in H9 as (H'2&Hr2&Hd2&Hs2); eauto. clear IHblks.
        2:{ rewrite idck_app in Hnd1. solve_NoDupMembers_app. }
        2:{ rewrite idckcaus_app, 2 idck_app in Hnd2. rewrite idck_app. solve_NoDup_app. }
        2:{ eapply Forall_impl; [|eapply H3]; intros. eapply NoDupLocals_incl; [|eauto]. solve_incl_app. }
        eapply H10 in H8 as (H'1&Hr1&Hd1&Hs1); eauto. clear H10.
        2:{ rewrite idck_app in Hnd1. solve_NoDupMembers_app. }
        2:{ rewrite idckcaus_app, 2 idck_app in Hnd2. rewrite idck_app. solve_NoDup_app. }
        2:{ eapply NoDupLocals_incl; [|eauto]. solve_incl_app. }
        exists (Env.union H'1 H'2). repeat split; eauto. rewrite map_app; auto.
        assert (NoDup (map fst (local_anon_in_block a) ++ map fst (flat_map local_anon_in_block blks))) as Hnd'.
        { rewrite <-map_app, <-fst_NoDupMembers.
          eapply (local_anons_in_block_NoDupMembers (a::blks)).
          apply NoDupMembers_app_r, NoDupMembers_idck in Hnd1; auto. }
        constructor; eauto. 2:eapply Forall_impl; [|eauto]; intros.
        1,2:eapply sem_block_refines. 2,4:eauto.
        eapply Env.union_refines3 in Hdom; eauto.
        eapply Env.union_refines4 in Hdom; eauto.
        1-2:rewrite idck_app, map_app in *; etransitivity; [|eauto]; solve_incl_app.
    Qed.

    Lemma sem_block_sem_block_ck : forall envP blk xs (env: list (ident * (clock * ident))) H bs,
        NoDupMembers (idty env ++ idck (anon_in_block blk)) ->
        NoDup (map snd (idck (env ++ idckcaus (locals blk)))) ->
        NoDupLocals (map fst env ++ map fst (anon_in_block blk)) blk ->
        VarsDefined blk xs ->
        incl xs (map fst env) ->
        incl (map snd (idck (env ++ idckcaus (locals blk)))) envP ->
        Env.dom H (map fst env) ->
        sc_vars (idty env) H bs ->
        wc_block G (idty env) blk ->
        sem_block_ck' G envP H bs blk ->
        exists H',
          Env.refines (@EqSt _) H H' /\
          Env.dom H' (map fst env ++ map fst (local_anon_in_block blk)) /\
          sem_block_ck G H' bs blk.
    Proof.
      induction blk using block_ind2;
        intros * Hnd1 Hnd2 Hnd3 Hvars Hincl HenvP Hdom Hsc Hwc Hsem;
        inv Hnd3; inv Hvars; inv Hwc; inv Hsem; simpl_ndup Hnd1.
      - (* equation *)
        rewrite app_nil_r in *.
        assert (Hsem:=H4). eapply sem_equation_anon in H4 as (H'&Href&Hdom'&Hanon); eauto.
        2:(rewrite map_fst_idty; auto).
        exists H'. repeat (split; auto).
        + rewrite map_fst_idty in Hdom'; auto.
        + econstructor; eauto.
          eapply sem_equation_anon_sem_equation_ck; eauto using Sem.sem_equation_refines, sc_vars_refines.
          eapply NoDupMembers_idty, NoDupMembers_app_l; eauto.
      - (* reset *)
        assert (forall k, exists H'k,
                     Env.refines (@EqSt _) (mask_hist k r H0) (mask_hist k r H'k) /\
                     Env.dom (mask_hist k r H'k) (map fst env0 ++ map fst (flat_map local_anon_in_block blocks)) /\
                     Forall (sem_block_ck G (mask_hist k r H'k) (maskb k r bs)) blocks) as Hbcks.
        { intros k.
          eapply sem_blocks_sem_blocks_ck with (H:=mask_hist k r H0) in H as (H'&Href&Hdom'&Hsem'); eauto.
          2:{ rewrite idck_app in Hnd1. solve_NoDupMembers_app. }
          2:{ eapply Forall_impl; [|eapply H3]. intros. eapply NoDupLocals_incl; eauto. solve_incl_app. }
          2:{ eapply Env.dom_map; eauto. }
          2:eapply sc_vars_mask; eauto.
          assert (slower_hist H' (maskb k r bs)) as Hslow.
          { eapply sc_vars_slower_hist.
            2:{ rewrite <-map_fst_idty, <-(map_fst_idck (flat_map _ _)), <-map_app in Hdom'; eauto. }
            eapply sc_vars_mask, sc_vars_refines in Hsc; eauto.
            apply Forall_app; split; auto.
            setoid_rewrite Forall_map. rewrite flat_map_concat_map. apply Forall_concat, Forall_map.
            eapply Forall_impl_In; [|eauto]; intros.
            apply sc_vars_local_anon_in_block in H1.
            2:{ rewrite Forall_forall in *. eapply NoDupLocals_incl; eauto.
                rewrite map_app. apply incl_appr, incl_appl, incl_map.
                etransitivity; [eapply local_anon_in_block_incl|].
                intros ??. apply in_flat_map; eauto. }
            unfold sc_vars, idck in *. now rewrite Forall_map in H1.
          }
          eapply slower_mask_hist in Hslow.
          exists H'. repeat (split; auto).
          3:(eapply Forall_impl; [|eauto]; intros;
             eapply sem_block_refines; [|eauto]).
          1-3:rewrite <- Hslow; auto.
        }
        eapply consolidate_mask_hist
          with (P := fun k H'k => Env.refines (@EqSt _) (mask_hist k r H0) H'k /\
                               Env.dom H'k (map fst env0 ++ map fst (flat_map local_anon_in_block blocks)) /\
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
        assert (Env.dom H'1 (map fst env0 ++ map fst (flat_map local_anon_in_block blocks))) as Hdom1.
        { specialize (HH' 0) as (_&Hdom1&_). setoid_rewrite Env.dom_map in Hdom1; eauto. }
        assert (Hsem2:=H6). eapply sem_exp_fresh in H6 as (H'2&Href2&Hdom2&Hanon2); eauto.
        2:{ rewrite fst_NoDupMembers, idck_app, 2 map_app, map_fst_idty, 2 map_fst_idck in Hnd1.
            solve_NoDup_app. }
        exists (Env.union H'1 H'2). repeat split; auto.
        econstructor; eauto.
        + eapply sem_exp_anon_sem_exp_ck. 3:eauto using sc_vars_refines. 1-5:eauto.
          * eapply NoDupMembers_idty, NoDupMembers_app_l; eauto.
          * rewrite idck_app in Hnd2. solve_NoDup_app.
          * eapply Sem.sem_exp_refines; [|eauto]; eauto.
          * eapply anon_sem_exp_refines; [|eauto].
            eapply Env.union_refines4'; eauto.
        + intros k.
          specialize (HH' k) as (_&_&Hsem').
          eapply Forall_impl; [|eapply Hsem']; intros.
          eapply sem_block_refines; [|eauto].
          eapply refines_mask.
          eapply Env.union_refines3 in Hdom; eauto.
          apply NoDupMembers_app_r, NoDupMembers_idck in Hnd1.
          rewrite <-map_app, <-fst_NoDupMembers.
          apply (local_anon_in_block_NoDupMembers (Breset blocks er)); auto.
      - (* locals *)
        rewrite app_nil_r in *.
        exists H0. repeat split; auto.
        assert (Env.dom_lb Hl (map fst locs)) as Hdomlb.
        { eapply Env.dom_lb_incl with (ys:=concat xs0). rewrite <-H8. apply incl_appl, incl_refl.
          eapply Env.dom_lb_concat, Forall_forall; eauto; intros ? Hin'.
          eapply Forall2_ignore1, Forall_forall in H4 as (?&?&?); eauto.
          rewrite Forall_forall in *.
          eapply sem_block_dom_lb; eauto using sem_block_ck'_sem_block.
          eapply NoDupLocals_incl; eauto.
          rewrite Permutation_app_comm, app_assoc. apply incl_appl.
          etransitivity; [eapply incl_concat; eauto|].
          rewrite <-H8. apply incl_app; [apply incl_appl, incl_refl|apply incl_appr; auto]. }
        assert (Env.refines (EqSt (A:=svalue)) H0 (Env.restrict (Env.union H0 Hl) (map fst env0 ++ map fst locs))) as Href1.
        { intros ?? Hfind.
          assert (In x (map fst env0)) as Hin by (eapply Env.dom_use; eauto; econstructor; eauto).
          destruct (Env.find x Hl) eqn:Hfind2.
          - do 2 esplit. 2:eapply Env.restrict_find, Env.union_find3'; eauto using in_or_app.
            eapply sem_var_det. econstructor; [eapply Hfind|reflexivity].
            eapply H7; eauto. econstructor; eauto; reflexivity.
            intro contra. eapply H6; eauto using in_or_app.
          - do 2 esplit. reflexivity.
            eapply Env.restrict_find, Env.union_find2; eauto using in_or_app. }
        assert (exists H', Env.refines (@EqSt _) (Env.restrict (Env.union H0 Hl) (map fst env0 ++ map fst locs))  H' /\
                      Env.dom H' (map fst (env0 ++ idckcaus locs) ++ map fst (flat_map local_anon_in_block blocks)) /\
                      Forall (sem_block_ck G H' bs) blocks) as (H'&Href&Hdom'&Hblks).
        { eapply sem_blocks_sem_blocks_ck; eauto.
          - rewrite idty_app, idty_idckcaus, <-app_assoc, (Permutation_app_comm (idck _)), app_assoc.
            apply NoDupMembers_app; auto.
            + apply NoDupMembers_idck, NoDupMembers_idty; auto.
            + intros x. rewrite InMembers_idck, InMembers_idty, fst_InMembers, map_app, map_fst_idty, map_fst_idck.
              intros ??. eapply H6; eauto.
          - rewrite idckcaus_app in Hnd2. now rewrite <-app_assoc.
          - rewrite map_app, <-app_assoc, map_fst_idckcaus.
            eapply Forall_impl; [|eapply H3]; intros.
            now rewrite (Permutation_app_comm (map fst locs)), app_assoc.
          - rewrite <-H8, map_app, map_fst_idckcaus, Permutation_app_comm.
            eapply incl_appl'; eauto.
          - etransitivity; [|eauto]. rewrite idckcaus_app, 4 idck_app. solve_incl_app.
          - rewrite map_app, map_fst_idckcaus. eapply Env.dom_lb_restrict_dom.
            eapply Env.union_dom_lb; eauto using Env.dom_dom_lb.
          - rewrite idty_app. apply Forall_app; split.
            + eapply sc_vars_refines; [|eauto]; eauto.
            + eapply sc_var_inv_sc_vars.
              * rewrite map_fst_idckcaus. eapply Forall_forall; intros.
                eapply Env.dom_lb_use in Hdomlb as (?&Hfind); eauto.
                do 2 eexists; try reflexivity.
                eapply Env.restrict_find, Env.union_find3'; eauto using in_or_app.
              * rewrite Forall_forall in *. intros ? Hin ??? Hin' Hvar.
                { eapply sem_clock_refines'.
                  - eapply H10; eauto. eapply in_map_iff in Hin' as ((?&(?&?)&?)&Heq&?); inv Heq.
                    repeat (eapply in_map_iff; do 2 esplit); eauto. reflexivity.
                  - intros ?? Hinm Hvar'. rewrite fst_InMembers, map_app, map_fst_idck, 2 map_fst_idty in Hinm.
                    eapply sem_var_restrict; eauto.
                  - eapply H14; eauto.
                    + eapply HenvP, incl_map; eauto. rewrite idckcaus_app, 2 idck_app. solve_incl_app.
                    + eapply sem_var_refines; [|eauto]. eapply Env.restrict_refines; eauto.
                }
          - now rewrite idty_app, idty_idckcaus.
          - eapply Forall_impl_In; [|eapply H13].
            intros ? Hin Hsem.
            rewrite <-map_fst_idckcaus, <-map_app, <-map_fst_idty.
            eapply Forall2_ignore2, Forall_forall in H4 as (?&?&?); eauto. rewrite Forall_forall in *.
            assert (NoDupLocals x a) as Hndl.
            { eapply NoDupLocals_incl; eauto.
              rewrite Permutation_app_comm, app_assoc. apply incl_appl.
              etransitivity; [eapply incl_concat; eauto|].
              rewrite <-H8. apply incl_app; [apply incl_appl, incl_refl|apply incl_appr; auto]. }
            eapply sem_block_ck'_restrict; eauto.
            + rewrite idty_app, idty_idckcaus; auto.
            + eapply sem_block_ck'_refines; [eauto|eauto| |eauto]. eapply Env.union_refines4'; eauto.
        }
        eapply Slocal with (H'0:=H'); eauto.
        + intros ?? Hvar Hnin1 Hnin2.
          assert (Env.In x H') as Hin. { inv Hvar. econstructor; eauto. }
          eapply Env.dom_use in Hin; eauto. rewrite map_app, map_fst_idckcaus, 2 in_app_iff in Hin.
          destruct Hin as [[Hin|Hin]|Hin]. 2,3:exfalso; apply fst_InMembers in Hin; eauto.
          eapply Env.dom_use in Hin; eauto. inv Hin. econstructor; eauto.
          eapply sem_var_det; eauto.
          do 2 (eapply sem_var_refines; eauto). econstructor; eauto; reflexivity.
        + rewrite map_app, map_fst_idckcaus, <-app_assoc in Hdom'.
          eapply local_hist_dom; eauto.
        + eapply sc_vars_refines; eauto.
          rewrite <-idty_idckcaus. eapply sc_var_inv_sc_vars.
          * rewrite map_fst_idckcaus. eapply Forall_forall; intros.
            eapply Env.dom_lb_use in Hdomlb as (?&Hfind); eauto.
            do 2 eexists; try reflexivity.
            eapply Env.restrict_find, Env.union_find3'; eauto using in_or_app.
          * rewrite Forall_forall in *. intros ? Hin ??? Hin' Hvar.
            { eapply sem_clock_refines'.
              - eapply H10; eauto. eapply in_map_iff in Hin' as ((?&(?&?)&?)&Heq&?); inv Heq.
                repeat (eapply in_map_iff; do 2 esplit); eauto. reflexivity.
              - intros ?? Hinm Hvar'. rewrite fst_InMembers, map_app, map_fst_idck, 2 map_fst_idty in Hinm.
                eapply sem_var_restrict; eauto.
              - eapply H14; eauto.
                + eapply HenvP, incl_map; eauto. rewrite idckcaus_app, 2 idck_app. solve_incl_app.
                + eapply sem_var_refines; [|eauto]. eapply Env.restrict_refines; eauto.
            }
    Qed.

  End sem_ck.

  Theorem sem_node_sem_node_ck {PSyn prefs} :
    forall (G : @global PSyn prefs),
      wc_global G ->
      Forall node_causal (nodes G) ->
      forall f ins outs,
        Sem.sem_node G f ins outs ->
        sem_clock_inputs G f ins ->
        sem_node_ck G f ins outs.
  Proof with eauto.
    intros (enums&nodes) Hwc.
    assert (Ordered_nodes (Global enums nodes)) as Hord by (eauto using wl_global_Ordered_nodes).
    revert Hwc Hord.
    induction nodes; intros Hwc Hord Hcaus ??? Hsem Hckins. now inversion Hsem.
    assert (Hsem' := Hsem).
    inversion_clear Hsem' as [? ? ? ? ? ? Hfind Hins Houts Heqs Hbk].
    pose proof (Lord.find_node_not_Is_node_in _ _ _ Hord Hfind) as Hnini.
    simpl in Hfind. destruct (ident_eq_dec (n_name a) f).
    - destruct Hckins as (?&?&Hfind'&Hins'&Hscin).
      rewrite find_node_now in Hfind'; auto. inv Hfind'.
      rewrite find_node_now in Hfind; auto. inv Hfind.
      eapply Sem.sem_block_cons in Heqs; eauto.
      assert (Hord':=Hord). inversion_clear Hord' as [|? ? Hord'' Hnneqs Hnn].
      inversion_clear Hwc as [|?? (Hwcn&_) Hwcg].
      inv Hcaus.
      assert (Hwcn':=Hwcn). destruct Hwcn' as (?&?&?).

      (* sem_clock H0 -> sem_clock H *)
      eapply sem_clocks_det' in Hscin; eauto. clear x Hins'.

      (* restrict H *)
      eapply sem_node_restrict in Heqs as (Hdom&Hins'&Houts'&Heqs'); eauto.
      remember (Env.restrict H (idents (n_in n ++ n_out n))) as H'.
      eapply sem_clocks_det with (ins:=n_out n) in Hscin; eauto. 2:rewrite Permutation_app_comm; eauto.
      clear H HeqH' Hins Houts.

      (* sc_vars H *)
      assert (wc_global (Global enums nodes0)) as Hvars by eauto.
      eapply sem_node_sc_vars in Hvars as (Hvars&Hloc); eauto.
      2:{ eapply det_global_n; eauto. }
      2:{ eapply sc_var_inv_intro; eauto. }

      (* sem_node_ck *)
      pose proof (n_defd n) as (?&Hdef&Hperm).
      eapply sem_block_sem_block_ck in Hloc as (H''&Href'&Hdom'&Hsem'); eauto.
      rewrite map_fst_idckcaus in Hdom'. rewrite idty_idckcaus in Hvars.
      eapply Snode with (H:=H''); eauto.
      + rewrite find_node_now; auto.
      + eapply Forall2_impl_In; [|eauto]; intros.
        eapply sem_var_refines; eauto.
      + eapply Forall2_impl_In; [|eauto]; intros.
        eapply sem_var_refines; eauto.
      + eapply sem_block_ck_cons'; eauto.
      + unfold clocked_node. split.
        * rewrite map_app, map_fst_idty; auto.
        * eapply sc_vars_refines; eauto.
      + eapply det_global_n; eauto.
      + rewrite idty_idckcaus, <-idck_app. apply NoDupMembers_idck, n_nodup.
      + rewrite <-idckcaus_app, <-app_assoc, idck_idckcaus. apply H2.
      + rewrite map_fst_idckcaus. apply n_nodup.
      + rewrite map_fst_idckcaus, Hperm. solve_incl_app.
      + rewrite <-idckcaus_app, <-app_assoc, idck_idckcaus. reflexivity.
      + rewrite map_fst_idckcaus; auto.
      + rewrite idty_idckcaus; auto.

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

  Lemma sem_exp_ck_sem_var {PSyn prefs} :
    forall (G: @global PSyn prefs) env H b e vs,
      wc_global G ->
      wc_exp G env e ->
      sem_exp_ck G H b e vs ->
      Forall2 (fun '(_, o) s => LiftO True (fun x : ident => sem_var H x s) o) (nclockof e) vs.
  Proof.
    intros * HwcG Hwc Hsem.
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

  Corollary sem_exps_ck_sem_var {PSyn prefs} :
    forall (G: @global PSyn prefs) env H b es vs,
      wc_global G ->
      Forall (wc_exp G env) es ->
      Forall2 (sem_exp_ck G H b) es vs ->
      Forall2 (fun '(_, o) s => LiftO True (fun x : ident => sem_var H x s) o) (nclocksof es) (concat vs).
  Proof.
    induction es; intros * HwcG Hwc Hsem; inv Hwc; inv Hsem; simpl; auto.
    apply Forall2_app; auto.
    eapply sem_exp_ck_sem_var; eauto.
  Qed.

  Lemma sc_outside_mask' {PSyn prefs} :
    forall (G: @global PSyn prefs) f n H b env ncks es rs ss vs bck sub,
      wc_global G ->
      find_node f G = Some n ->
      Forall (wc_exp G env) es ->
      Forall2 (sem_exp_ck G H b) es ss ->
      (forall k, sem_node_ck G f (map (maskv k rs) (concat ss)) (map (maskv k rs) vs)) ->
      Forall2 (fun '(_, o) (s : Stream svalue) => LiftO True (fun x0 : ident => sem_var H x0 s) o) ncks vs ->
      Forall2 (sem_clock H b) (clocksof es) (map abstract_clock (concat ss)) ->
      Forall2 (WellInstantiated bck sub) (idck (idty (n_in n))) (nclocksof es) ->
      Forall2 (WellInstantiated bck sub) (idck (idty (n_out n))) ncks ->
      Forall2 (sem_clock H b) (map fst ncks) (map abstract_clock vs).
  Proof.
    intros * HwcG Hfind Hwc Hseme Hsem Hvars Hcki Hwi Hwo.
    eapply sc_outside_mask with (rs0:=rs) (es0:=es); eauto.
    2,3:eapply wc_find_node in HwcG as (?&?&?&?); eauto.
    - eapply sem_exps_ck_sem_var; eauto.
    - intros k.
      specialize (Hsem k). inv Hsem. rewrite Hfind in H1; inv H1.
      exists H0. repeat split; eauto.
      destruct H6 as (?&Hinv). clear - H3 Hinv. unfold sc_vars in Hinv.
      unfold idents, idck, idty in *.
      rewrite 2 Forall2_map_1, Forall2_map_2. rewrite Forall2_map_1 in H3.
      eapply Forall2_impl_In; [|eauto]; intros (?&?&?) ? Hin _ Hvar.
      rewrite 2 Forall_map in Hinv. eapply Forall_forall in Hinv; eauto using in_or_app.
      destruct Hinv as (?&Hvar'&Hck).
      eapply sem_var_det in Hvar; eauto.
      rewrite <-Hvar; eauto.
  Qed.

  Fact sc_exps' {PSyn prefs} : forall (G : @global PSyn prefs) H b env es ss,
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

  Lemma sc_exp {PSyn prefs} : forall (G : @global PSyn prefs) env H b e vs,
      wc_global G ->
      sc_vars env H b ->
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
          eapply sem_exps_ck_sem_exps, sem_exps_numstreams in H4. 3,4:eauto. 2:eauto with datatypes.
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
            - eapply sem_exps_ck_sem_exps, sem_exps_numstreams in H3. 3,4:eauto.
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

  Corollary sc_exps {PSyn prefs} : forall (G : @global PSyn prefs) H b env es ss,
      wc_global G ->
      sc_vars env H b ->
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
    Context {PSyn1 PSyn2 : block -> Prop}.
    Context {pref1 pref2 : PS.t}.

    (** We develop a notion of refinement over globals :
        [node_sem_refines G G' f] means that if [f] exists and has a given semantic in [G],
        then it also exists and has the same semantic in [G'].
        This is just a shorthand definition, but is useful when proving the correctness
        of transformation passes over the Lustre AST.
     *)
    Definition node_sem_refines (G : @global PSyn1 pref1) (G' : @global PSyn2 pref2) f : Prop :=
      forall ins outs, sem_node_ck G f ins outs -> sem_node_ck G' f ins outs.

    Definition global_sem_refines (G : @global PSyn1 pref1) (G' : @global PSyn2 pref2) : Prop :=
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

    Fact sem_ref_sem_block : forall G G' blk H b,
        global_sem_refines G G' ->
        sem_block_ck G H b blk ->
        sem_block_ck G' H b blk.
    Proof.
      induction blk using block_ind2; intros * Href Hsem;
        inv Hsem.
      - (* equation *)
        constructor; eauto using sem_ref_sem_equation.
      - (* reset *)
        econstructor; eauto using sem_ref_sem_exp.
        intros k. specialize (H8 k).
        rewrite Forall_forall in *; eauto.
      - (* local *)
        econstructor; eauto.
        rewrite Forall_forall in *; eauto.
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
    Context {PSyn : block -> Prop}.
    Context {prefs : PS.t}.

    Import List.

    Lemma Forall2_sem_exp_absent: forall (f : list (Stream svalue) -> list (Stream svalue)) (G : @global PSyn prefs) H b es ss,
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

    Lemma sem_var_absent_inv : forall H x v,
        sem_var (Env.map (fun _ => Streams.const absent) H) x v ->
        exists v', sem_var H x v' /\ v ≡ Streams.const absent.
    Proof.
      intros * Var. inv Var.
      unfold Env.MapsTo in *. rewrite Env.Props.P.F.map_o in H1.
      apply option_map_inv in H1 as (?&?&?); subst.
      do 2 esplit; eauto. econstructor; eauto. reflexivity.
    Qed.

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

    Lemma sem_clock_inputs_false : forall (G : @global PSyn prefs) f xs,
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
      forall (G : @global PSyn prefs) H bs bck,
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
      - (* Blocal *)
        eapply Slocal with (H'0:=Env.map (fun _ => Streams.const absent) H'); eauto.
        + intros * Hsemv Hinm1 Hinm2.
          eapply sem_var_absent_inv in Hsemv as (?&Hvar&Heq).
          eapply H1 in Hvar; eauto.
          rewrite Heq. eapply sem_var_absent; eauto.
        + rewrite Env.dom_map.
          eapply Env.dom_intro. intros.
          eapply Env.dom_use in H2. rewrite H2, 3 in_app_iff.
          apply or_iff_compat_r.
          now rewrite <-2 fst_InMembers, <-2 Env.In_Members, Env.Props.P.F.map_in_iff.
        + eapply Forall_impl; [|eauto]; intros (?&?) (?&?&?).
          do 2 esplit; eauto using sem_var_absent.
          rewrite ac_Streams_const. eapply sem_clock_absent; eauto.
      - (* Node *)
        econstructor. 5:reflexivity. 1-4:eauto; subst.
        1,2:(rewrite Forall2_map_2; eapply Forall2_impl_In; [|eauto];
             intros; eapply sem_var_absent; eauto).
        + rewrite clocks_of_false; auto.
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
