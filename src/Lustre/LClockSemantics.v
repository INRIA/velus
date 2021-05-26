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
From Velus Require Import Lustre.LSyntax Lustre.LTyping Lustre.LClocking Lustre.LCausality Lustre.LOrdered Lustre.LSemantics.

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
       (Import IStr  : INDEXEDSTREAMS Ids Op OpAux Cks)
       (Import Sem   : LSEMANTICS Ids Op OpAux Cks Syn Lord CStr).

  Import CStr.
  Module Import CIStr := CoindIndexedFun Ids Op OpAux Cks CStr IStr.

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
      Env.refines eq H H' ->
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

  (** ** Alignment proof extracted from Transcription/Correctness.v *)

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
      + repeat rewrite_Forall_forall. eapply H2...
    - (* arrow *)
      econstructor...
      + repeat rewrite_Forall_forall. eapply H0...
      + repeat rewrite_Forall_forall. eapply H1...
      + repeat rewrite_Forall_forall. eapply H2...
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

  Corollary sem_equations_restrict {prefs} : forall (G : @global prefs) vars H b eqs,
      Forall (wc_equation G vars) eqs ->
      Forall (sem_equation G H b) eqs ->
      Forall (sem_equation G (Env.restrict H (List.map fst vars)) b) eqs.
  Proof.
    intros * Hwc Hsem.
    eapply Forall_Forall in Hwc; eauto. clear Hsem.
    eapply Forall_impl; [|eauto]. intros ? [? ?].
    eapply sem_equation_restrict; eauto.
  Qed.

  (** * Alignment proof *)

  (** ** Semantics with anonymous variables in the history *)
  (** The case of applications is annoying to handle in the proof : because
      of clock dependencies, clock streams can sometimes be built from anonymous
      streams (which are not in the history)
      We prove that we can give the semantics of a node with these anonymous streams
      named in the history.
      This allows for simpler reasoning down the line *)
  Section AnonSemantics.

    Context {prefs : PS.t}.
    Variable G : @global prefs.

    Inductive sem_exp_anon : history -> Stream bool -> exp -> list (Stream svalue) -> Prop :=
    | Sconst:
        forall H b c cs,
          cs ≡ const b c ->
          sem_exp_anon H b (Econst c) [cs]

    | Senum:
        forall H b k ty es,
          es ≡ enum b k ->
          sem_exp_anon H b (Eenum k ty) [es]

    | Svar:
        forall H b x s ann,
          sem_var H x s ->
          sem_exp_anon H b (Evar x ann) [s]

    | Sunop:
        forall H b e op ty s o ann,
          sem_exp_anon H b e [s] ->
          typeof e = [ty] ->
          lift1 op ty s o ->
          sem_exp_anon H b (Eunop op e ann) [o]

    | Sbinop:
        forall H b e1 e2 op ty1 ty2 s1 s2 o ann,
          sem_exp_anon H b e1 [s1] ->
          sem_exp_anon H b e2 [s2] ->
          typeof e1 = [ty1] ->
          typeof e2 = [ty2] ->
          lift2 op ty1 ty2 s1 s2 o ->
          sem_exp_anon H b (Ebinop op e1 e2 ann) [o]

    | Sfby:
        forall H b e0s es er anns s0ss sss sr r os,
          Forall2 (sem_exp_anon H b) e0s s0ss ->
          Forall2 (sem_exp_anon H b) es sss ->
          Forall2 (fun e r => sem_exp_anon H b e [r]) er sr ->
          bools_ofs sr r ->
          Forall3 (fun s0 s1 o => fby s0 s1 r o) (concat s0ss) (concat sss) os ->
          sem_exp_anon H b (Efby e0s es er anns) os

    | Sarrow:
        forall H b e0s es er anns s0ss sss sr r os,
          Forall2 (sem_exp_anon H b) e0s s0ss ->
          Forall2 (sem_exp_anon H b) es sss ->
          Forall2 (fun e r => sem_exp_anon H b e [r]) er sr ->
          bools_ofs sr r ->
          Forall3 (fun s0 s1 o => arrow s0 s1 r o) (concat s0ss) (concat sss) os ->
          sem_exp_anon H b (Earrow e0s es er anns) os

    | Swhen:
        forall H b x s k es lann ss os,
          Forall2 (sem_exp_anon H b) es ss ->
          sem_var H x s ->
          Forall2 (fun s' => when k s' s) (concat ss) os ->
          sem_exp_anon H b (Ewhen es x k lann) os

    | Smerge:
        forall H b x tx s es lann vs os,
          sem_var H x s ->
          Forall2 (Forall2 (sem_exp_anon H b)) es vs ->
          Forall2Transpose (merge s) (List.map (@concat _) vs) os ->
          sem_exp_anon H b (Emerge (x, tx) es lann) os

    | Scase:
        forall H b e s es d lann vs vd os,
          sem_exp_anon H b e [s] ->
          Forall2 (fun oes vs => forall es, oes = Some es -> Forall2 (sem_exp_anon H b) es vs) es vs ->
          Forall2 (fun oes vs => oes = None -> Forall2 EqSts vs vd) es vs ->
          Forall2 (sem_exp_anon H b) d vd ->
          Forall2Transpose (case s) (List.map (@concat _) vs) os ->
          sem_exp_anon H b (Ecase e es d lann) os

    | Sapp:
        forall H b f es er lann ss os rs bs,
          Forall2 (sem_exp_anon H b) es ss ->
          Forall2 (fun e r => sem_exp_anon H b e [r]) er rs ->
          bools_ofs rs bs ->
          (forall k, sem_node G f (List.map (mask k bs) (concat ss)) (List.map (mask k bs) os)) ->
          Forall2 (fun '(_, (_, o)) s => LiftO True (fun x => sem_var H x s) o) lann os ->
          sem_exp_anon H b (Eapp f es er lann) os

    with sem_equation_anon: history -> Stream bool -> equation -> Prop :=
           Seq:
             forall H b xs es ss,
               Forall2 (sem_exp_anon H b) es ss ->
               Forall2 (sem_var H) xs (concat ss) ->
               sem_equation_anon H b (xs, es).

    Hint Constructors sem_exp_anon sem_equation_anon.

    Fact sem_exp_anon_refines : forall b e H H' v,
      Env.refines eq H H' ->
      sem_exp_anon H b e v ->
      sem_exp_anon H' b e v.
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
        eapply Forall2_impl_In; eauto.
        intros [? [? [?|]]] ? ? ? ?; simpl in *; auto.
        eapply sem_var_refines...
    Qed.

    Fact sem_equation_anon_refines : forall H H' b equ,
        Env.refines eq H H' ->
        sem_equation_anon H b equ ->
        sem_equation_anon H' b equ.
    Proof with eauto.
      intros H H' b eq Href Hsem.
      destruct Hsem.
      econstructor.
      + eapply Forall2_impl_In; [| eauto].
        intros. eapply sem_exp_anon_refines...
      + eapply Forall2_impl_In; [| eauto].
        intros. eapply sem_var_refines...
    Qed.

    (** *** sem_exp_anon -> sem_exp *)

    Lemma sem_exp_anon_sem_exp : forall H b e vs,
        sem_exp_anon H b e vs ->
        sem_exp G H b e vs.
    Proof.
      induction e using exp_ind2; intros * Hsem; inv Hsem; econstructor; eauto.
      9:clear H12.
      1-12:(eapply Forall2_impl_In; [|eauto]; subst;
            intros ? ? Hin ? ?; eapply Forall_forall in Hin; eauto;
            simpl in Hin; eauto).
      - eapply Forall2_impl_In; [|eauto]; intros.
        eapply Forall_forall in Hin; [|eauto]; eauto.
      - simpl in *. intros; subst; simpl in *.
        eapply Forall2_impl_In; [|eauto]; intros.
        eapply Forall_forall in Hin; eauto.
    Qed.
    Hint Resolve sem_exp_anon_sem_exp.

    Lemma sem_exps_anon_sem_exps : forall H b es vs,
        Forall2 (sem_exp_anon H b) es vs ->
        Forall2 (sem_exp G H b) es vs.
    Proof.
      intros * Hsem.
      eapply Forall2_impl_In; [|eauto]; intros; eauto.
    Qed.
    Hint Resolve sem_exps_anon_sem_exps.

    Lemma sem_equation_anon_sem_equation : forall H b equ,
        sem_equation_anon H b equ ->
        sem_equation G H b equ.
    Proof.
      intros * Heq. inv Heq.
      econstructor; eauto.
    Qed.

    (** *** sem_exp -> sem_exp_anon *)

    Local Ltac simpl_ndup Hnd :=
        simpl in *;
        try rewrite app_nil_r in Hnd; repeat rewrite map_app.
    Local Ltac ndup_l H := rewrite app_assoc in H; apply NoDupMembers_app_l in H; auto.
    Local Ltac ndup_r H := rewrite Permutation_swap in H; apply NoDupMembers_app_r in H; auto.

    Hint Resolve Env.union_refines2 Env.union_dom Env.adds_opt'_refines Env.adds_opt'_dom.

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

    Fact sem_exps_sem_exps_fresh' : forall env H b es vs,
      Forall
        (fun e => forall vs,
             Env.dom H (map fst env) ->
             NoDupMembers (env ++ fresh_in e) ->
             wl_exp G e ->
             sem_exp G H b e vs ->
             exists H',
               Env.refines eq H H' /\ Env.dom H' (map fst env ++ map fst (fresh_in e)) /\ sem_exp_anon H' b e vs) es ->
      Env.dom H (map fst env) ->
      NoDupMembers (env ++ fresh_ins es) ->
      Forall (wl_exp G) es ->
      Forall2 (sem_exp G H b) es vs ->
      exists H', Env.refines eq H H' /\
            Env.dom H' (map fst env ++ map fst (fresh_ins es)) /\
            Forall2 (sem_exp_anon H' b) es vs.
    Proof.
      induction es; intros * Hf Hdom Hnd Hwl Hsem;
        inv Hwl; inv Hsem; inv Hf.
      - simpl_ndup Hnd. exists H; auto.
      - unfold fresh_ins in Hnd; simpl_ndup Hnd.
        eapply IHes in H7 as (H'2&Hr2&Hd2&Hs2); eauto. 2:ndup_r Hnd. clear IHes.
        eapply H5 in H4 as (H'1&Hr1&Hd1&Hs1); eauto. 2:ndup_l Hnd. clear H5.
        exists (Env.union H'1 H'2). repeat split; auto.
        apply NoDupMembers_app_r, fst_NoDupMembers in Hnd. rewrite map_app in Hnd.
        constructor; eauto. 2:eapply Forall2_impl_In; [|eauto]; intros.
        1,2:eapply sem_exp_anon_refines; [|eauto].
        eapply Env.union_refines3 in Hdom; eauto.
        eapply Env.union_refines4 in Hdom; eauto.
    Qed.

    Corollary sem_exps_sem_exps_fresh'': forall env H b es vs,
        Forall
          (Forall
             (fun e => forall vs,
                  Env.dom H (map fst env) ->
                  NoDupMembers (env ++ fresh_in e) ->
                  wl_exp G e ->
                  sem_exp G H b e vs ->
                  exists H' : Env.t (Stream svalue),
                    Env.refines eq H H' /\ Env.dom H' (map fst env ++ map fst (fresh_in e)) /\ sem_exp_anon H' b e vs)) es ->
        Env.dom H (map fst env) ->
        NoDupMembers (env ++ flat_map fresh_ins es) ->
        Forall (Forall (wl_exp G)) es ->
        Forall2 (Forall2 (sem_exp G H b)) es vs ->
        exists H' : Env.t (Stream svalue),
          Env.refines eq H H' /\ Env.dom H' (map fst env ++ map fst (flat_map fresh_ins es)) /\
          Forall2 (Forall2 (sem_exp_anon H' b)) es vs.
    Proof.
      induction es; intros * Hf Hdom Hnd Hwl Hsem;
        inv Hwl; inv Hsem; inv Hf.
      - simpl_ndup Hnd. exists H; auto.
      - simpl_ndup Hnd.
        eapply IHes in H7 as (H'2&Hr2&Hd2&Hs2); eauto. 2:ndup_r Hnd. clear IHes.
        eapply sem_exps_sem_exps_fresh' in H5 as (H'1&Hr1&Hd1&Hs1); eauto. 2:ndup_l Hnd.
        exists (Env.union H'1 H'2). repeat split; auto.
        apply NoDupMembers_app_r, fst_NoDupMembers in Hnd. rewrite map_app in Hnd.
        constructor; auto.
        2:eapply Forall2_impl_In; [|eauto]; intros.
        1,2:eapply Forall2_impl_In; [|eauto]; intros.
        1,2:eapply sem_exp_anon_refines; [|eauto].
        eapply Env.union_refines3 in Hdom; eauto.
        eapply Env.union_refines4 in Hdom; eauto.
    Qed.

    Corollary sem_exps_sem_exps_fresh''': forall env H b brs vs,
        Forall
          (LiftO True
             (Forall
                (fun e => forall vs,
                     Env.dom H (map fst env) ->
                     NoDupMembers (env ++ fresh_in e) ->
                     wl_exp G e ->
                     sem_exp G H b e vs ->
                     exists H' : Env.t (Stream svalue),
                       Env.refines eq H H' /\ Env.dom H' (map fst env ++ map fst (fresh_in e)) /\ sem_exp_anon H' b e vs))) brs ->
        NoDupMembers (env ++ flat_map (or_default_with [] fresh_ins) brs) ->
        Env.dom H (map fst env) ->
        (forall es, In (Some es) brs -> Forall (wl_exp G) es) ->
        Forall2 (fun oes vs => forall es, oes = Some es -> Forall2 (sem_exp G H b) es vs) brs vs ->
        exists H' : Env.t (Stream svalue),
          Env.refines eq H H' /\
          Env.dom H' (map fst env ++ map fst (flat_map (or_default_with [] fresh_ins) brs)) /\
          Forall2 (fun oes vs => forall es, oes = Some es -> Forall2 (sem_exp_anon H' b) es vs) brs vs.
    Proof.
      induction brs; intros * Hf Hnd Hdom Hwl Hsem; inv Hsem; inv Hf.
      - simpl_ndup Hnd. exists H. auto.
      - simpl_ndup Hnd.
        eapply IHbrs in H5 as (H'2&Hr2&Hd2&Hs2); eauto. 2:ndup_r Hnd. clear IHbrs.
        destruct a; simpl in *.
        + eapply sem_exps_sem_exps_fresh' in H3 as (H'1&Hr1&Hd1&Hs1); eauto. 2:ndup_l Hnd.
          exists (Env.union H'1 H'2). repeat split; auto.
          apply NoDupMembers_app_r, fst_NoDupMembers in Hnd. rewrite map_app in Hnd.
          constructor; auto. intros ? Heq; inv Heq.
          2:eapply Forall2_impl_In; [|eauto]; intros.
          1,2:eapply Forall2_impl_In; [|eauto]; intros.
          1,2:eapply sem_exp_anon_refines; [|eauto].
          eapply Env.union_refines3 in Hdom; eauto.
          eapply Env.union_refines4 in Hdom; eauto.
        + exists H'2. repeat split; auto.
          constructor; auto. intros ? Heq. inv Heq.
    Qed.

    Lemma sem_exp_sem_exp_fresh : forall env H b e vs,
        Env.dom H (map fst env) ->
        NoDupMembers (env ++ fresh_in e) ->
        wl_exp G e ->
        sem_exp G H b e vs ->
        exists H', Env.refines eq H H' /\
              Env.dom H' (map fst env ++ map fst (fresh_in e)) /\
              sem_exp_anon H' b e vs.
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
        1,2:eapply sem_exp_anon_refines; [|eauto].
        eapply Env.union_refines3 in Hdom; eauto.
        eapply Env.union_refines4 in Hdom; eauto.
      - (* fby *)
        eapply sem_exps_sem_exps_fresh' in H0 as (H'0&Hr0&Hd0&Hs0); eauto. 2:ndup_l Hnd.
        eapply sem_exps_sem_exps_fresh' in H1 as (H'1&Hr1&Hd1&Hs1); eauto. 2:ndup_r Hnd; ndup_l Hnd.
        eapply sem_exps_sem_exps_fresh' in H2 as (H'2&Hr2&Hd2&Hs2); eauto. 2:ndup_r Hnd; ndup_r Hnd.
        2:eapply Forall2_map_2; eapply H19. rewrite Forall2_map_2 in Hs2. clear H19.
        exists (Env.union H'0 (Env.union H'1 H'2)). repeat split; auto 10.
        apply NoDupMembers_app_r, fst_NoDupMembers in Hnd.
        repeat rewrite map_app in Hnd.
        econstructor; eauto.
        1-3:eapply Forall2_impl_In; [|eauto]; simpl; intros; eapply sem_exp_anon_refines; [|eauto].
        eapply Env.union_refines3 with (m:=H). 1-6:eauto.
        etransitivity. 2:eapply Env.union_refines4 with (m:=H). eapply Env.union_refines3 with (m:=H).
        2-6,8-12:eauto. 2:eauto. apply NoDup_app_r in Hnd; auto.
        etransitivity. 2:eapply Env.union_refines4 with (m:=H). eapply Env.union_refines4 with (m:=H).
        2-6,8-12:eauto. 2:eauto. apply NoDup_app_r in Hnd; auto.
      - (* arrow *)
        eapply sem_exps_sem_exps_fresh' in H0 as (H'0&Hr0&Hd0&Hs0); eauto. 2:ndup_l Hnd.
        eapply sem_exps_sem_exps_fresh' in H1 as (H'1&Hr1&Hd1&Hs1); eauto. 2:ndup_r Hnd; ndup_l Hnd.
        eapply sem_exps_sem_exps_fresh' in H2 as (H'2&Hr2&Hd2&Hs2); eauto. 2:ndup_r Hnd; ndup_r Hnd.
        2:eapply Forall2_map_2; eapply H19. rewrite Forall2_map_2 in Hs2. clear H19.
        exists (Env.union H'0 (Env.union H'1 H'2)). repeat split; auto 10.
        apply NoDupMembers_app_r, fst_NoDupMembers in Hnd.
        repeat rewrite map_app in Hnd.
        econstructor; eauto.
        1-3:eapply Forall2_impl_In; [|eauto]; simpl; intros; eapply sem_exp_anon_refines; [|eauto].
        eapply Env.union_refines3 with (m:=H). 1-6:eauto.
        etransitivity. 2:eapply Env.union_refines4 with (m:=H). eapply Env.union_refines3 with (m:=H).
        2-6,8-12:eauto. 2:eauto. apply NoDup_app_r in Hnd; auto.
        etransitivity. 2:eapply Env.union_refines4 with (m:=H). eapply Env.union_refines4 with (m:=H).
        2-6,8-12:eauto. 2:eauto. apply NoDup_app_r in Hnd; auto.
      - (* when *)
        eapply sem_exps_sem_exps_fresh' in H0 as (H'1&Hr1&Hd1&Hs1); eauto.
        exists H'1. repeat split; auto.
        econstructor; eauto.
        eapply sem_var_refines; eauto.
      - (* merge *)
        eapply sem_exps_sem_exps_fresh'' in H0 as (H'1&Hr1&Hd1&Hs1); eauto.
        exists H'1. repeat split; auto.
        econstructor; eauto.
        eapply sem_var_refines; eauto.
      - (* case *)
        eapply IHe in H14 as (H'0&Hr0&Hd0&Hsd0); eauto. 2:do 2 ndup_l Hnd.
        eapply sem_exps_sem_exps_fresh''' in H0 as (H'1&Hr1&Hd1&Hs1); eauto. 2:ndup_r Hnd; ndup_l Hnd.
        eapply sem_exps_sem_exps_fresh' in H20 as (H'2&Hr2&Hd2&Hsd2); eauto. 2:do 2 ndup_r Hnd.
        exists (Env.union H'0 (Env.union H'1 H'2)); repeat split; auto.
        econstructor; eauto.
        2:clear H17 H19; do 2 (eapply Forall2_impl_In; [|eauto]; intros; subst).
        3:eapply Forall2_impl_In; [|eauto]; intros; subst.
        1-3:eapply sem_exp_anon_refines; [|eauto].
        eapply Env.union_refines3 in Hdom; eauto.
        2:etransitivity; [eapply Env.union_refines3 in Hdom; eauto|eapply Env.union_refines4 in Hdom; eauto].
        4:etransitivity; [|eapply Env.union_refines4 in Hdom; eauto]; [eapply Env.union_refines4 in Hdom; eauto|].
        1,3,5:(eapply NoDupMembers_app_r in Hnd;
               repeat rewrite <-map_app; rewrite <-fst_NoDupMembers; auto).
        1,2:(eapply NoDupMembers_app_r, NoDupMembers_app_r in Hnd;
             repeat rewrite <-map_app; rewrite <-fst_NoDupMembers; auto).
      - (* app *)
        eapply sem_exps_sem_exps_fresh' in H0 as (H'0&Hr0&Hd0&Hs0); eauto. 2:ndup_l Hnd.
        eapply sem_exps_sem_exps_fresh' in H1 as (H'1&Hr1&Hd1&Hs1); eauto. 2:ndup_r Hnd; ndup_l Hnd.
        2:eapply Forall2_map_2; eapply H17. rewrite Forall2_map_2 in Hs1. clear H17.
        assert (length vs = length a) as Hlen.
        { specialize (H19 0). inv H19. rewrite H1 in H10; inv H10.
          apply Forall2_length in H3. unfold idents in H3. repeat rewrite map_length in H3.
          congruence. }
        remember (Env.adds_opt' (anons a) vs (Env.union H'0 H'1)) as H'3.
        rewrite fst_NoDupMembers in Hnd. repeat rewrite map_app in Hnd.
        assert (Env.refines eq (Env.union H'0 H'1) H'3) as Hr3.
        { subst. eapply Env.adds_opt'_refines.
          + unfold anons. rewrite map_length; eauto.
          + repeat rewrite app_assoc in Hnd. rewrite (Permutation_app_comm _ (map fst (Syn.anon_streams a))) in Hnd.
            repeat rewrite <- app_assoc in Hnd.
            eapply Forall_forall; intros; subst.
            eapply anons_In in H0. eapply NoDup_app_In in Hnd; eauto.
            erewrite Env.dom_use; eauto.
        }
        exists H'3. repeat split; auto.
        + etransitivity; [|eauto]. eauto.
        + rewrite HeqH'3, <- anons_anon_streams, app_assoc, app_assoc.
          eapply Env.adds_opt'_dom; eauto.
          unfold anons. rewrite map_length; auto.
          repeat rewrite <- app_assoc. eauto.
        + econstructor; eauto.
          * eapply Forall2_impl_In; [|eauto]; intros.
            eapply sem_exp_anon_refines; [|eauto]. etransitivity; eauto.
            eapply Env.union_refines3 in Hd1; eauto.
            apply NoDup_app_r in Hnd. rewrite app_assoc in Hnd. apply NoDup_app_l in Hnd; auto.
          * eapply Forall2_impl_In; [|eauto]; intros; simpl in *.
            eapply sem_exp_anon_refines; [|eauto]. etransitivity; eauto.
            eapply Env.union_refines4 in Hd1; eauto.
            apply NoDup_app_r in Hnd. rewrite app_assoc in Hnd. apply NoDup_app_l in Hnd; auto.
          * assert (Forall2 (fun o v => forall x, o = Some x -> Env.find x H'3 = Some v) (anons a) vs) as Hvs.
            { eapply all_In_Forall2; eauto. unfold anons; rewrite map_length; auto.
              intros ? ? Hin ? ?; subst.
              eapply Env.In_find_adds_opt'; eauto.
              eapply anons_NoDup, NoDup_app_r, NoDup_app_r, NoDup_app_r; eauto. }
            clear - Hvs.
            unfold anons in Hvs. rewrite Forall2_map_1 in Hvs.
            induction Hvs; intros; constructor; auto.
            destruct x as (?&?&?). destruct o; simpl; auto.
            econstructor. eapply H. 1,2:reflexivity.
    Qed.

    Lemma sem_exp_sem_exp_anon : forall env H b e vs,
        Env.dom H (map fst env) ->
        NoDupMembers (env ++ anon_in e) ->
        Forall2 (fun '(_, (_, o)) s => LiftO True (fun x : ident => sem_var H x s) o) (annot e) vs ->
        wl_exp G e ->
        sem_exp G H b e vs ->
        exists H', Env.refines eq H H' /\
          Env.dom H' (map fst env ++ map fst (anon_in e)) /\
          sem_exp_anon H' b e vs.
    Proof.
      intros * Hdom Hndup Hf Hwl Hsem.
      destruct e; simpl in *.
      1-10:eapply sem_exp_sem_exp_fresh in Hsem; eauto.
      inv Hwl; inv Hsem.
      - (* app *)
        eapply sem_exps_sem_exps_fresh' in H13 as (H'1&Hr1&?&?); eauto. 3:ndup_l Hndup.
        2:{ eapply Forall_forall; intros * Hin ?????.
            eapply sem_exp_sem_exp_fresh; eauto. }
        eapply Forall2_map_2 in H15.
        eapply sem_exps_sem_exps_fresh' in H15 as (H'2&Hr2&?&?); eauto. 3:ndup_r Hndup.
        2:{ eapply Forall_forall; intros * Hin ?????.
            eapply sem_exp_sem_exp_fresh; eauto. }
        assert (Env.dom (Env.union H'1 H'2) (map fst env0 ++ map fst (fresh_ins l) ++ map fst (fresh_ins l0))) as Hd3 by eauto.
        exists (Env.union H'1 H'2). repeat split; auto.
        + repeat rewrite map_app. eauto.
        + rewrite fst_NoDupMembers, map_app, map_app in Hndup.
          econstructor; eauto.
          * eapply Forall2_impl_In; [|eauto]. intros.
            eapply sem_exp_anon_refines; [|eauto].
            eapply Env.union_refines3 in H2; eauto. apply NoDup_app_r in Hndup; auto.
          * rewrite Forall2_map_2 in H3.
            eapply Forall2_impl_In; [|eapply H3]; simpl in *. intros.
            eapply sem_exp_anon_refines; [|eauto].
            eapply Env.union_refines4 in H2; eauto. apply NoDup_app_r in Hndup; auto.
          * eapply Forall2_impl_In; eauto.
            intros (?&?&[?|]) ? ? ? ?; simpl in *; auto.
            eapply sem_var_refines; [|eauto]. eauto.
    Qed.

    Corollary sem_exps_sem_exps_anon : forall env H b es vs,
        Env.dom H (map fst env) ->
        NoDupMembers (env ++ anon_ins es) ->
        Forall2 (fun '(_, (_, o)) s => LiftO True (fun x : ident => sem_var H x s) o) (annots es) (concat vs) ->
        Forall (wl_exp G) es ->
        Forall2 (sem_exp G H b) es vs ->
        exists H', Env.refines eq H H' /\
          Env.dom H' (map fst env ++ map fst (anon_ins es)) /\
          Forall2 (sem_exp_anon H' b) es vs.
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
        eapply sem_exp_sem_exp_anon in H0 as (H'1&?&?&?); eauto. 2:ndup_l Hnd.
        exists (Env.union H'1 H'2). repeat split; auto.
        + rewrite map_app; auto.
        + apply NoDupMembers_app_r, fst_NoDupMembers in Hnd. rewrite map_app in Hnd.
          constructor; auto.
          2:eapply Forall2_impl_In; [|eauto]; intros.
          1,2:eapply sem_exp_anon_refines; [|eauto].
          eapply Env.union_refines3 in Hdom; eauto.
          eapply Env.union_refines4 in Hdom; eauto.
    Qed.

    Lemma sem_equation_sem_equation_anon : forall env H b equ,
        Env.dom H (map fst env) ->
        NoDupMembers (env ++ anon_in_eq equ) ->
        wc_equation G (idck env) equ ->
        sem_equation G H b equ ->
        exists H', Env.refines eq H H' /\
          Env.dom H' (map fst env ++ map fst (anon_in_eq equ)) /\
          sem_equation_anon H' b equ.
    Proof.
      intros ? ? ? (xs&es) Hdom Hnd Hwc Hsem.
      destruct Hwc as (Hwc1&Hwc2&_). inv Hsem.
      eapply sem_exps_sem_exps_anon in H5 as (H'&?&?&?); eauto.
      - exists H'. repeat split; eauto. econstructor; eauto.
        eapply Forall2_impl_In; [|eauto].
        intros * ? ? ?. eapply sem_var_refines; eauto.
      - clear - Hwc2 H6.
        rewrite Forall2_swap_args, nclocksof_annots, Forall2_map_1 in Hwc2.
        eapply Forall2_trans_ex in H6; [|eauto]. clear - H6.
        eapply Forall2_impl_In; eauto. intros (?&?&?) ??? (?&?&?&?).
        destruct o; simpl in *; subst; auto.
    Qed.

    Lemma sem_equations_sem_equations_anon : forall env H b eqs,
        Env.dom H (map fst env) ->
        NoDupMembers (env ++ anon_in_eqs eqs) ->
        Forall (wc_equation G (idck env)) eqs ->
        Forall (sem_equation G H b) eqs ->
        exists H', Env.refines eq H H' /\
          Env.dom H' (map fst env ++ map fst (anon_in_eqs eqs)) /\
          Forall (sem_equation_anon H' b) eqs.
    Proof.
      induction eqs; intros * Hdom Hnd Hwc Hsem; simpl in *; inv Hwc; inv Hsem.
      - exists H. repeat split; auto.
      - unfold anon_in_eqs in *; simpl in *.
        eapply IHeqs in H5 as (H'2&?&?&?); eauto. 2:ndup_r Hnd.
        eapply sem_equation_sem_equation_anon in H2 as (H'1&?&?&?); eauto. 2:ndup_l Hnd.
        exists (Env.union H'1 H'2). repeat split; auto.
        + rewrite map_app; auto.
        + apply NoDupMembers_app_r, fst_NoDupMembers in Hnd. rewrite map_app in Hnd.
          constructor; auto.
          2:eapply Forall_impl; [|eauto]; intros [? ?] ?.
          1,2:eapply sem_equation_anon_refines; [|eauto].
          eapply Env.union_refines3 in Hdom; eauto.
          eapply Env.union_refines4 in Hdom; eauto.
    Qed.

    (** Properties of sem_exp_anon *)

    Lemma sem_exp_anon_sem_var : forall env H b e vs,
        wc_exp G env e ->
        sem_exp_anon H b e vs ->
        Forall2 (fun '(_, o) s => LiftO True (fun x : ident => sem_var H x s) o) (nclockof e) vs.
    Proof.
      intros * Hwc Hsem.
      assert (length vs = length (nclockof e)) as Hlen.
      { rewrite length_nclockof_numstreams. eapply sem_exp_numstreams; eauto. }
      inv Hwc; inv Hsem; simpl in *.
      1-6:constructor; simpl; auto.
      - (* fby *)
        clear - Hlen H6. rewrite map_length in Hlen; symmetry in Hlen.
        eapply Forall2_ignore2' in H6; eauto.
        clear Hlen. induction H6; simpl; constructor; auto.
        destruct x as [? [? [?|]]]; simpl; auto. inv H0.
      - (* arrow *)
        clear - Hlen H6. rewrite map_length in Hlen; symmetry in Hlen.
        eapply Forall2_ignore2' in H6; eauto.
        clear Hlen. induction H6; simpl; constructor; auto.
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
        clear - H18.
        rewrite Forall2_map_1.
        eapply Forall2_impl_In; eauto. intros (?&?&?) ? ? ? ?; eauto.
    Qed.

    Corollary sem_exps_anon_sem_var : forall env H b es vs,
        Forall (wc_exp G env) es ->
        Forall2 (sem_exp_anon H b) es vs ->
        Forall2 (fun '(_, o) s => LiftO True (fun x : ident => sem_var H x s) o) (nclocksof es) (concat vs).
    Proof.
      induction es; intros * Hwc Hsem; inv Hwc; inv Hsem; simpl; auto.
      apply Forall2_app; auto.
      eapply sem_exp_anon_sem_var; eauto.
    Qed.
  End AnonSemantics.

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
      1,2:exfalso; eapply sem_var_instant_det in Hsemv; eauto; congruence.
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
      2,4,6:(unfold sem_var_instant in *;
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
    - inv Hinst. eapply sem_clock_instant_det in Hck; eauto. rewrite Hck; auto.
    - inversion Hinst as [Hcase]. cases_eqn Hcase. inv Hcase.
      inv Hck.
      1,2:econstructor;eauto. 5:eapply IStr.Son_abs2; eauto.
      2,4,6:(unfold sem_var_instant in *;
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

  (* induction hypothesis over the program *)
  Definition sc_nodes {prefs} (G : @global prefs) : Prop :=
    forall H f n xs (* vs *) os,
      sem_node G f xs os ->
      find_node f G = Some n ->
      Forall2 (sem_var H) (idents (n_in n)) xs ->
      Forall2 (sem_var H) (idents (n_out n)) os ->
      Forall2 (fun xc => sem_clock H (clocks_of xs) (snd xc))
              (idck (n_in n)) (map abstract_clock xs) ->
      Forall2 (fun xc => sem_clock H (clocks_of xs) (snd xc))
              (idck (n_out n)) (map abstract_clock os).
  Hint Unfold sc_nodes.

  Lemma inst_in_eqst:
    forall H Hi bck sub xs ys vs i ck,
      In (i, ck) xs ->
      Forall2 (WellInstantiated bck sub) xs ys ->
      Forall2 (sem_var Hi) (map fst xs) vs ->
      Forall2 (fun '(_, o) s => LiftO True (fun x => sem_var H x s) o) ys vs ->
      forall i',
        sub i = Some i' ->
        orel (@EqSt svalue) (Env.find i Hi) (Env.find i' H).
  Proof.
    intros * Hin WI Hsvi Hsvo i Sub.
    rewrite Forall2_map_1 in Hsvi.
    rewrite Forall2_swap_args in Hsvo.
    eapply Forall2_trans_ex with (1:=Hsvi) in Hsvo. clear Hsvi.
    eapply Forall2_Forall2 in WI; eauto. clear Hsvo.
    eapply Forall2_forall2 in WI as [? WI].
    eapply In_nth in Hin as [n [Hlen Hin]].
    destruct (nth n ys (Cbase, None)) eqn:Hy.
    specialize (WI (xH, Cbase) (Cbase, None) _ _ _ Hlen Hin Hy) as ((?&?&?&?)&Hinst).
    simpl in H2; inv H2. apply Env.find_1 in H5; rewrite H5.
    inv Hinst; simpl in *. rewrite Sub in H2; inv H2.
    simpl in H3; inv H3. apply Env.find_2 in H7; rewrite H7.
    constructor. etransitivity; eauto. symmetry; auto.
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

  (* When function call parameters are well instantiated and have
     the [sem_clock] property, we obtain the same property inside
     the node (Hi = "H inside").
   *)
  Lemma sc_inside {prefs1 prefs2} :
    forall (G : @global prefs1) H Hi b env es ss0 bck sub (n : @node prefs2),
      Forall (wc_exp G env) es ->
      Forall2 (sem_exp_anon G H b) es ss0 ->
      wc_env (idck (n_in n)) ->
      Forall2 (sem_clock H b) (clocksof es) (map abstract_clock (concat ss0)) ->
      Forall2 (WellInstantiated bck sub) (idck (n_in n)) (nclocksof es) ->
      Forall2 (sem_var Hi) (idents (n_in n)) (concat ss0) ->
      Forall2 (fun xc => sem_clock Hi (clocks_of (concat ss0)) (snd xc))
              (idck (n_in n)) (map abstract_clock (concat ss0)).
  Proof.
    intros * Hwc Hse WCin Hscin WIi Hsv.

    rewrite clocksof_nclocksof, Forall2_map_1 in Hscin.
    apply Forall2_trans_ex with (1 := WIi) in Hscin as H1.
    eapply Forall2_impl_In; eauto.
    intros (x & ck) xs  Hxin ? ((yck & ny) & Hyin & (Hsub & Hinst) & Hsc).
    simpl in *.
    eapply sc_inst'; eauto.
    - eapply sc_has_base; eauto.
    - clear - Hwc Hxin WCin WIi Hse Hsv.
      intros i i' Free Sub.
      pose proof (wc_env_free_in_clock _ _ _ _ WCin Hxin Free) as [].
      eapply inst_in_eqst; eauto. eauto.
      rewrite idck_idents in Hsv; eauto.
      eapply sem_exps_anon_sem_var in Hse; eauto.
  Qed.

  Lemma sc_outside {prefs1 prefs2} :
    forall (G : @global prefs1) H Hi es b env ncks ss0 ss bck sub (n : @node prefs2),
      Forall (wc_exp G env) es ->
      Forall2 (sem_exp_anon G H b) es ss0 ->
      Forall2 (fun '(_, o) s => LiftO True (fun x0 => sem_var H x0 s) o) ncks ss ->
      wc_env (idck (n_in n)) ->
      wc_env (idck (n_in n ++ n_out n)) ->
      Forall2 (sem_clock H b) (clocksof es) (map abstract_clock (concat ss0)) ->
      Forall2 (sem_var Hi) (idents (n_in n)) (concat ss0) ->
      Forall2 (WellInstantiated bck sub) (idck (n_in n)) (nclocksof es) ->
      Forall2 (WellInstantiated bck sub) (idck (n_out n)) ncks ->
      Forall2 (fun xc => sem_clock Hi (clocks_of (concat ss0)) (snd xc))
              (idck (n_out n)) (map abstract_clock ss) ->
      Forall2 (sem_var Hi) (idents (n_out n)) ss ->
      Forall2 (sem_clock H b) (map fst ncks) (map abstract_clock ss).
  Proof.
    intros * Hwc Hse1 Hse2 WCin WCinout Hscin Hsvi WIi WIo Hscout Hsvo.

    rewrite clocksof_nclocksof, Forall2_map_1 in Hscin.
    rewrite Forall2_map_1.
    rewrite Forall2_swap_args in WIo.
    eapply Forall2_trans_ex with (1:=WIo) in Hscout.
    eapply Forall2_impl_In; eauto.
    intros (x & ck) xs  Hxin ? ((yck & ny) & Hyin & (Hsub & Hinst) & Hsc).
    simpl in *.
    eapply sc_inst; eauto.
    - eapply sc_has_base; eauto.
    - clear - Hwc Hyin WCin WCinout WIi WIo Hse1 Hse2 Hsvi Hsvo.
      intros i i' Free Sub.
      assert (In (yck, ny) (idck (n_in n ++ n_out n))) as Hyin2.
      { rewrite idck_app. apply in_or_app; auto. }
      pose proof (wc_env_free_in_clock _ _ _ _ WCinout Hyin2 Free) as [].
      rewrite <- Forall2_swap_args in WIo.
      eapply inst_in_eqst. 1,5:eauto.
      + rewrite idck_app. eapply Forall2_app; eauto.
      + rewrite idck_app, map_app. repeat rewrite <- idck_idents.
        eapply Forall2_app; eauto.
      + eapply Forall2_app; eauto. eapply sem_exps_anon_sem_var; eauto.
  Qed.

  Lemma sc_inst_mask:
    forall H' b b' ck ck' bck sub cks rs,
      instck bck sub ck = Some ck' ->
      sem_clock H' b' bck b ->
      (forall k, exists H, sem_clock H (maskb k rs b) ck (maskb k rs cks) /\
                 (forall x x',
                     Is_free_in_clock x ck ->
                     sub x = Some x' ->
                     orel (fun v1 v2 => EqSt v1 (mask k rs v2)) (Env.find x H) (Env.find x' H'))) ->
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
      eapply tr_history_find_orel_mask' with (n:=n) in Henv.
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
      2,4,6:(unfold sem_var_instant in *;
             specialize (Henv' i i0 (FreeCon1 _ _ _) Hcase1); rewrite H5 in Henv';
             inv Henv'; auto).
      * rewrite H4 in *; eapply IHck in Hcase0; eauto.
      * rewrite H4 in *; eapply IHck in Hcase0; eauto.
      * eapply IHck with (cks:=Streams.const true) in Hcase0; eauto.
        rewrite const_nth in Hcase0; auto. rewrite const_nth; eauto.
  Qed.

  Lemma sc_inst_mask':
    forall H H' b b' ck ck' bck sub cks k rs,
      instck bck sub ck = Some ck' ->
      sem_clock H' b' ck' cks ->
      sem_clock H' b' bck b ->
      (forall x x',
          Is_free_in_clock x ck ->
          sub x = Some x' ->
          orel (fun v1 v2 => EqSt v1 (mask k rs v2)) (Env.find x H) (Env.find x' H')) ->
      sem_clock H (maskb k rs b) ck (maskb k rs cks).
  Proof.
    intros * Hinst Hck Hbck Henv.
    rewrite sem_clock_equiv in *.
    intros n. specialize (Hck n). specialize (Hbck n).
    assert (forall x x' n, Is_free_in_clock x ck -> sub x = Some x' -> orel (fun v1 v2 => v1 = (if (CStr.count rs) # n =? k then v2 else absent)) (Env.find x (CIStr.tr_history H n)) (Env.find x' (CIStr.tr_history H' n))) as Henv'.
    { intros * Hfree Hsub. specialize (Henv x x' Hfree Hsub).
      eapply tr_history_find_orel_mask' in Henv; eauto. } clear Henv.
    unfold tr_Stream in *.
    revert H H' b b' ck' bck cks sub Hinst Hck Hbck Henv'.
    induction ck; intros; simpl in *.
    - inv Hinst.
      repeat rewrite maskb_nth in *. destruct (_ =? k); auto.
      eapply sem_clock_instant_det in Hck; eauto.
      rewrite Hck; auto.
    - inversion Hinst as [Hcase]. cases_eqn Hcase. inv Hcase.
      repeat rewrite maskb_nth in *; destruct (_ =? k) eqn:Hcount.
      + inv Hck.
        1,2:econstructor;eauto. 5:eapply IStr.Son_abs2; eauto.
        2,4,6:(unfold sem_var_instant in *;
               specialize (Henv' i i0 n (FreeCon1 _ _ _) Hcase1); rewrite H5 in Henv';
               inv Henv'; auto; rewrite Hcount; auto).
        * rewrite H4 in *; eapply IHck with (b':=b') in Hcase0; eauto.
          repeat rewrite maskb_nth, Hcount, <- H4 in Hcase0. rewrite <- H4; eauto.
        * rewrite H4 in *; eapply IHck with (b':=b') in Hcase0; eauto.
          repeat rewrite maskb_nth, Hcount in Hcase0; eauto.
        * assert (Htrue:=H4). apply sem_clock_instant_true_inv in H4; eauto.
          eapply IHck with (b:=b) (b':=b') (cks:=Streams.const true) in Hcase0; eauto.
          repeat rewrite maskb_nth, Hcount in Hcase0. rewrite const_nth in Hcase0; eauto.
          rewrite const_nth; eauto.
      + inv Hck.
        1,2,3:econstructor; eauto.
        2,4,6:(unfold sem_var_instant in *;
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
      Forall2 (sem_var Hi) (map fst xs) (map (mask k rs) vs) ->
      Forall2 (fun '(_, o) s => LiftO True (fun x => sem_var H x s) o) ys vs ->
      forall i',
        sub i = Some i' ->
        orel (fun v1 v2 => v1 ≡ mask k rs v2) (Env.find i Hi) (Env.find i' H).
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

  Corollary sc_inside_mask {prefs1 prefs2} :
    forall (G : @global prefs1) H Hi b env es ss0 bck sub (n : @node prefs2) k rs,
      Forall (wc_exp G env) es ->
      Forall2 (sem_exp_anon G H b) es ss0 ->
      wc_env (idck (n_in n)) ->
      Forall2 (sem_clock H b) (clocksof es) (map abstract_clock (concat ss0)) ->
      Forall2 (WellInstantiated bck sub) (idck (n_in n)) (nclocksof es) ->
      Forall2 (sem_var Hi) (idents (n_in n)) (map (mask k rs) (concat ss0)) ->
      Forall2 (fun xc => sem_clock Hi (clocks_of (map (mask k rs) (concat ss0))) (snd xc))
              (idck (n_in n)) (map abstract_clock (map (mask k rs) (concat ss0))).
  Proof.
    intros * Hwc Hse WCin Hscin WIi Hsv.

    rewrite Forall2_map_2 in Hscin. rewrite Forall2_map_2 in Hsv. repeat rewrite Forall2_map_2.
    rewrite clocksof_nclocksof, Forall2_map_1 in Hscin.
    apply Forall2_trans_ex with (1 := WIi) in Hscin as H1.
    eapply Forall2_impl_In; eauto.
    intros (x & ck) xs  Hxin ? ((yck & ny) & Hyin & (Hsub & Hinst) & Hsc).
    simpl in *.
    rewrite ac_mask, clocks_of_mask.
    eapply sc_inst_mask'; eauto.
    - eapply sc_has_base; eauto.
      rewrite Forall2_map_2; auto.
    - clear - Hwc Hxin WCin WIi Hse Hsv.
      intros i i' Free Sub.
      pose proof (wc_env_free_in_clock _ _ _ _ WCin Hxin Free) as [].
      eapply inst_in_eqst_mask; eauto.
      rewrite <- idck_idents, Forall2_map_2; eauto.
      eapply sem_exps_anon_sem_var in Hse; eauto.
  Qed.

  Definition def_stream b := enum b 0.

  Lemma sc_outside_mask {prefs1 prefs2} :
    forall (G : @global prefs1) H es b env ncks ss0 ss bck sub (n : @node prefs2) rs,
      Forall (wc_exp G env) es ->
      Forall2 (sem_exp_anon G H b) es ss0 ->
      Forall2 (fun '(_, o) s => LiftO True (fun x0 => sem_var H x0 s) o) ncks ss ->
      wc_env (idck (n_in n)) ->
      wc_env (idck (n_in n ++ n_out n)) ->
      Forall2 (sem_clock H b) (clocksof es) (map abstract_clock (concat ss0)) ->
      Forall2 (WellInstantiated bck sub) (idck (n_in n)) (nclocksof es) ->
      Forall2 (WellInstantiated bck sub) (idck (n_out n)) ncks ->
      (forall k, exists Hi,
            Forall2 (fun xc => sem_clock Hi (clocks_of (map (mask k rs) (concat ss0))) (snd xc))
                    (idck (n_out n)) (map abstract_clock (map (mask k rs) ss)) /\
            Forall2 (sem_var Hi) (idents (n_in n)) (map (mask k rs) (concat ss0)) /\
            Forall2 (sem_var Hi) (idents (n_out n)) (map (mask k rs) ss)) ->
      Forall2 (sem_clock H b) (map fst ncks) (map abstract_clock ss).
  Proof.
    intros * Hwc Hse1 Hse2 WCin WCinout Hscin WIi WIo Hk.

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
        * eapply Forall2_app; eauto. eapply sem_exps_anon_sem_var; eauto.
  Qed.

  Section sc_inv.
    Context {prefs : PS.t}.
    Variable (G : @global prefs).

    Definition sc_var_inv env (H : history) (b : Stream bool) : ident -> Prop :=
      fun x => forall ck xs,
          In (x, ck) env ->
          sem_var H x xs ->
          sem_clock H b ck (abstract_clock xs).

    Definition sc_exp_inv env (H : history) (b : Stream bool) : exp -> nat -> Prop :=
      fun e k => forall ss,
          wc_exp G env e ->
          sem_exp_anon G H b e ss ->
          sem_clock H b (nth k (clockof e) Cbase) (abstract_clock (nth k ss (def_stream b))).

    Fact P_exps_sc_exp_inv : forall env H b es ss k,
        Forall (wc_exp G env) es ->
        Forall2 (sem_exp_anon G H b) es ss ->
        LCA.P_exps (sc_exp_inv env H b) es k ->
        sem_clock H b (nth k (clocksof es) Cbase) (abstract_clock (nth k (concat ss) (def_stream b))).
    Proof.
      induction es; intros * Hwc Hsem Hp;
        inv Hwc; inv Hsem; simpl. inv Hp.
      assert (length y = numstreams a) as Hlen by (eapply sem_exp_numstreams, sem_exp_anon_sem_exp; eauto).
      inv Hp.
      - (* now *)
        rewrite app_nth1. 2:rewrite length_clockof_numstreams; auto.
        rewrite app_nth1. 2:congruence.
        eapply H8; eauto.
      - (* later *)
        rewrite app_nth2. 1,2:rewrite length_clockof_numstreams; auto.
        rewrite app_nth2. 1,2:rewrite Hlen; auto.
    Qed.

    Fact P_exps_sc_exp_inv_all : forall env H b es ss,
        Forall (wc_exp G env) es ->
        Forall2 (sem_exp_anon G H b) es ss ->
        (forall k, k < length (annots es) -> LCA.P_exps (sc_exp_inv env H b) es k) ->
        Forall2 (sem_clock H b) (clocksof es) (map abstract_clock (concat ss)).
    Proof.
      intros * Hwc Hsem Hk.
      assert (length (clocksof es) = length (concat ss)) as Hlen.
      { rewrite length_clocksof_annots. symmetry.
        eapply sem_exps_numstreams, sem_exps_anon_sem_exps; eauto. }
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
      intros * ? Hwc Hsem; inv Hsem.
      symmetry in H4. rewrite <- ac_const; eauto.
      constructor. reflexivity.
    Qed.

    Lemma sc_exp_enum : forall env H b k ty,
        sc_exp_inv env H b (Eenum k ty) 0.
    Proof.
      intros * ? Hwc Hsem; inv Hsem.
      symmetry in H6. rewrite <- ac_enum; eauto.
      constructor. reflexivity.
    Qed.

    Lemma sc_exp_var : forall env H b x ann,
        sc_var_inv env H b x ->
        sc_exp_inv env H b (Evar x ann) 0.
    Proof.
      intros *  Hvar ss Hwc Hsem; inv Hsem; simpl.
      eapply Hvar; eauto. inv Hwc; auto.
    Qed.

    Lemma sc_exp_unop : forall env H b op e1 ann,
        sc_exp_inv env H b e1 0 ->
        sc_exp_inv env H b (Eunop op e1 ann) 0.
    Proof.
      intros * He1 ss Hwc Hsem; inv Hwc; inv Hsem; simpl.
      specialize (He1 [s] H2 H8); rewrite H4 in He1; simpl in He1.
      rewrite <- ac_lift1; eauto.
    Qed.

    Lemma sc_exp_binop : forall env H b op e1 e2 ann,
        sc_exp_inv env H b e1 0 ->
        sc_exp_inv env H b e2 0 ->
        sc_exp_inv env H b (Ebinop op e1 e2 ann) 0.
    Proof.
      intros * He1 He2 ss Hwc Hsem; inv Hwc; inv Hsem; simpl.
      specialize (He1 [s1] H4 H9); rewrite H6 in He1; simpl in He1.
      rewrite <- ac_lift2; eauto.
    Qed.

    Lemma sc_exp_fby : forall env H b e0s es er ann k,
        k < length ann ->
        LCA.P_exps (sc_exp_inv env H b) e0s k ->
        (forall k0 : nat, k0 < length (annots er) -> LCA.P_exps (sc_exp_inv env H b) er k0) ->
        sc_exp_inv env H b (Efby e0s es er ann) k.
    Proof.
      intros * Hk Hexps _ ss Hwc Hsem; simpl.
      inv Hwc. inv Hsem.
      eapply P_exps_sc_exp_inv in Hexps; eauto.
      rewrite Forall2_eq in H7. rewrite H7.
      assert (Forall2 (fun x y => abstract_clock x ≡ abstract_clock y) (concat s0ss) ss).
      { clear - H19. eapply Forall3_ignore2 in H19.
        eapply Forall2_impl_In; eauto.
        intros ? ? _ _ [? ?]. apply ac_fby1 in H; auto. }
      apply Forall2_forall2 in H0 as [_ Hac].
      erewrite <- Hac; eauto.
      erewrite sem_exps_numstreams, <- length_clocksof_annots, <- H7, map_length; eauto.
      eapply sem_exps_anon_sem_exps; eauto.
    Qed.

    Lemma sc_exp_arrow : forall env H b e0s es er ann k,
        k < length ann ->
        LCA.P_exps (sc_exp_inv env H b) e0s k ->
        LCA.P_exps (sc_exp_inv env H b) es k ->
        (forall k0 : nat, k0 < length (annots er) -> LCA.P_exps (sc_exp_inv env H b) er k0) ->
        sc_exp_inv env H b (Earrow e0s es er ann) k.
    Proof.
      intros * Hk He0s Hes _ ss Hwc Hsem; simpl.
      inv Hwc. inv Hsem.
      eapply P_exps_sc_exp_inv in He0s; eauto.
      rewrite Forall2_eq in H7. rewrite H7.
      assert (Forall2 (fun x y => abstract_clock x ≡ abstract_clock y) (concat s0ss) ss).
      { clear - H19. eapply Forall3_ignore2 in H19.
        eapply Forall2_impl_In; eauto.
        intros ? ? _ _ [? ?]. apply ac_arrow1 in H; auto. }
      apply Forall2_forall2 in H0 as [_ Hac].
      erewrite <- Hac; eauto.
      erewrite sem_exps_numstreams, <- length_clocksof_annots, <- H7, map_length; eauto.
      eapply sem_exps_anon_sem_exps; eauto.
    Qed.

    Lemma sc_exp_when : forall env H b es x b' ann k,
        k < length (fst ann) ->
        LCA.P_exps (sc_exp_inv env H b) es k ->
        sc_var_inv env H b x ->
        sc_exp_inv env H b (Ewhen es x b' ann) k.
    Proof.
      intros * Hk Hes Hvar ss Hwc Hsem; simpl.
      inv Hwc. inv Hsem.
      eapply P_exps_sc_exp_inv in Hes; eauto.
      assert (Hv:=H13). eapply Hvar in Hv; eauto.
      erewrite map_nth' with (d':=OpAux.bool_velus_type); eauto.
      unfold clock_of_nclock, stripname; simpl.
      eapply Forall_forall in H6. 2:eapply nth_In; rewrite <- H7; eauto.
      eapply sc_when in Hes; eauto. erewrite H6; eauto.
      eapply Forall2_forall2 in H14 as [_ Hwhen].
      eapply Hwhen; eauto.
      replace (length (concat ss0)) with (length (annots es)). rewrite <- length_clocksof_annots, <- H7; eauto.
      symmetry. eapply sem_exps_numstreams, sem_exps_anon_sem_exps; eauto.
    Qed.

    Lemma sc_exp_merge : forall env H b x tx es ann k,
        k < length (fst ann) ->
        sc_var_inv env H b x ->
        Forall (fun es => LCA.P_exps (sc_exp_inv env H b) es k) es ->
        sc_exp_inv env H b (Emerge (x, tx) es ann) k.
    Proof.
      intros * Hk Hvar Hes ss Hwc Hsem; simpl.
      inv Hwc. inv Hsem.
      eapply Forall2Transpose_nth with (k0:=k) (d1:=def_stream b) (d2:=def_stream b) in H15.
      2:{ eapply Forall2Transpose_length in H15. inv H14; try congruence.
          inv H15. inv H8. inv H6.
          eapply sem_exps_anon_sem_exps, sem_exps_numstreams in H0; eauto.
          rewrite <- H9, H0, <-length_clocksof_annots, <- H11; auto.
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
        eapply P_exps_sc_exp_inv in Sem; eauto.
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
      intros * Hk He Hes ss Hwc Hsem; simpl.
      inv Hwc. inv Hsem.
      eapply Forall2Transpose_nth with (k0:=k) (d1:=def_stream b) (d2:=def_stream b) in H21.
      2:{ eapply Forall2Transpose_length in H21. inv H17; try congruence.
          inv H21. rewrite <-H13.
          destruct x; simpl in *.
          - eapply sem_exps_anon_sem_exps, sem_exps_numstreams in H0. 3:eauto.
            2:eauto.
            rewrite H0, <-length_clocksof_annots.
            rewrite <-H9; eauto.
          - inv H19. specialize (H17 eq_refl). eapply sem_exps_anon_sem_exps, sem_exps_numstreams in H20; eauto.
            erewrite concat_length_eq. 2:eapply Forall2_impl_In; [|eauto]; intros; eapply Forall2_length; eauto.
            rewrite H20, <-length_clocksof_annots. congruence.
      }
      eapply ac_case in H21. rewrite <-H21.
      eapply He in H14; eauto.
      rewrite H5 in H14; simpl in H14.
      erewrite map_nth' with (d':=OpAux.bool_velus_type); eauto.
    Qed.

    Lemma sc_exp_app : forall env H b f es er ann k,
        wc_global G ->
        sc_nodes G ->
        k < length ann ->
        (forall k0 : nat, k0 < length (annots es) -> LCA.P_exps (sc_exp_inv env H b) es k0) ->
        sc_exp_inv env H b (Eapp f es er ann) k.
    Proof.
      intros * HwcG HscG Hlen Hk' ? Hwc Hsem; simpl.
      inv Hwc. inv Hsem.
      eapply wc_find_node in HwcG as [G' (WcIn&WcInOut&_)]; eauto.

      (* Arguments *)
      assert (Hse:=H11). eapply P_exps_sc_exp_inv_all in Hse; eauto.

      (* Returning aligned values *)
      eapply sc_outside_mask with (ncks:=map snd ann0) in H11; eauto.
      2:rewrite Forall2_map_1; eapply Forall2_impl_In; eauto; intros [? [? ?]] ? ? ? ?; eauto.
      - eapply Forall2_forall2 in H11 as [? Hck].
        repeat rewrite map_length in *.
        specialize (Hck Cbase (abstract_clock (def_stream b)) _ _ _ Hlen eq_refl eq_refl).
        rewrite map_nth, map_map in Hck; eauto.
      - (* Returning aligned values *)
        intros k'.
        specialize (H17 k'). inv H17. rewrite H1 in H6; inv H6.
        exists H0. repeat split; eauto.
        eapply sc_inside_mask in WcIn. 3-6:eauto. 2:eauto.
        eapply HscG in H1; eauto. econstructor; eauto.
    Qed.

    Lemma sc_exp_equation : forall n H b xs es k,
        k < length xs ->
        wc_node G n ->
        In (xs, es) (n_eqs n) ->
        Forall (sem_equation_anon G H b) (n_eqs n) ->
        LCA.P_exps (sc_exp_inv (idck (n_in n ++ n_vars n ++ n_out n)) H b) es k ->
        sc_var_inv (idck (n_in n ++ n_vars n ++ n_out n)) H b (nth k xs xH).
    Proof.
      intros * Hk Hwc Hin Hsem Hexps ? ? Hin' Hvar.
      destruct Hwc as (_&_&_&Hwc).
      eapply Forall_forall in Hwc; eauto. destruct Hwc as (Hwc1&_&Hwc2).
      eapply Forall_forall in Hsem; eauto. inv Hsem.
      eapply P_exps_sc_exp_inv in Hexps; eauto.
      assert (nth k (clocksof es) Cbase = ck); subst.
      { eapply Forall2_forall2 in Hwc2 as [_ HIn'].
        specialize (HIn' xH Cbase _ _ _ Hk eq_refl eq_refl).
        specialize (node_NoDup n) as Hndup.
        rewrite <- fst_NoDupMembers, <- NoDupMembers_idck in Hndup.
        eapply NoDupMembers_det in Hndup; eauto. }
      assert (xs0 ≡ nth k (concat ss) (def_stream b)) as Hequiv.
      { eapply Forall2_forall2 in H6 as [_ Hvar'].
        specialize (Hvar' xH (def_stream b) _ _ _ Hk eq_refl eq_refl).
        eapply sem_var_det in Hvar'; eauto. }
      rewrite Hequiv; auto.
    Qed.

    Lemma sc_vars :
      forall n H b,
        wc_global G ->
        sc_nodes G ->
        wc_node G n ->
        LCA.node_causal n ->
        Forall (sc_var_inv (idck (n_in n ++ n_vars n ++ n_out n)) H b) (map fst (n_in n)) ->
        Forall (sem_equation_anon G H b) (n_eqs n) ->

        Forall (sc_var_inv (idck (n_in n ++ n_vars n ++ n_out n)) H b) (map fst (n_in n ++ n_vars n ++ n_out n)).
    Proof.
      intros n H b HwcG HscG Hwcn Hcau Hins Hsemn.
      eapply LCA.node_causal_ind
        with (P_var:=sc_var_inv _ H b)
             (P_exp:=sc_exp_inv _ H b); eauto.
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
      - intros. eapply sc_exp_equation; eauto.
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
      assert (Forall2 (fun x => sem_var_instant (CIStr.tr_history H n) (fst x)) (ins ++ outs)
                      (map (fun x => tr_Stream x n) (vins ++ vouts))) as Ho.
      { rewrite Forall2_map_2. eapply Forall2_impl_In; [|eapply Ho1]. intros (?&?&?) ? ? ? ?.
        eapply CIStr.sem_var_impl in H2; eauto. } clear Ho1.
      assert (Forall2 (fun x => sem_var_instant (CIStr.tr_history H' n) (fst x)) (ins ++ outs)
                      (map (fun x => tr_Stream x n) (vins ++ vouts))) as Ho'.
      { rewrite Forall2_map_2. eapply Forall2_impl_In; [|eapply Ho2]. intros (?&?&?) ? ? ? ?.
        eapply CIStr.sem_var_impl in H2; eauto. } clear Ho2.
      assert (Forall (fun '(x, _) => forall v, sem_var_instant (CIStr.tr_history H n) x v -> sem_var_instant (CIStr.tr_history H' n) x v)
                     (idck ins ++ idck outs)) as Hvars.
      { unfold idck. rewrite <- map_app, Forall_map.
        eapply Forall2_Forall2 in Ho; [|eapply Ho']. clear Ho'.
        eapply Forall2_ignore2 in Ho.
        eapply Forall_impl; [|eauto]. intros (?&?&?) (?&?&?&?).
        intros ? Hvar. eapply sem_var_instant_det in H2; eauto; subst. assumption.
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

    Fact sem_equation_In : forall H b eqs,
        Forall (sem_equation G H b) eqs ->
        Forall (fun v => Env.In v H) (vars_defined eqs).
    Proof.
      induction eqs; intros Hsem; inv Hsem; simpl.
      - constructor.
      - destruct a; simpl.
        inv H2.
        apply Forall_app. split; auto.
        apply sem_var_In in H8; auto.
    Qed.

    Lemma sem_node_restrict {prefs2} : forall (n : @node prefs2) H b xs ys,
        Forall (wc_equation G (idck (n_in n ++ n_vars n ++ n_out n))) (n_eqs n) ->
        Forall2 (sem_var H) (idents (n_in n)) xs ->
        Forall2 (sem_var H) (idents (n_out n)) ys ->
        Forall (sem_equation G H b) (n_eqs n) ->
        let H' := Env.restrict H (idents (n_in n ++ n_vars n ++ n_out n)) in
        Env.dom H' (idents (n_in n ++ n_vars n ++ n_out n)) /\
        Forall2 (sem_var H') (idents (n_in n)) xs /\
        Forall2 (sem_var H') (idents (n_out n)) ys /\
        Forall (sem_equation G H' b) (n_eqs n).
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
          assert (In x (vars_defined (n_eqs n))) as HIn'.
          { eapply Permutation_in in Hdef;[eauto|].
            rewrite map_app. apply in_or_app... }
          apply sem_equation_In in Heqs. rewrite Forall_forall in Heqs...
        + apply sem_var_In in Houts. rewrite Forall_forall in Houts...
      - eapply Forall2_impl_In; [|eauto]; intros.
        unfold idents in H0. apply in_map_iff in H0 as ((?&?&?)&?&?); simpl in *; subst.
        eapply sem_var_restrict; eauto.
        rewrite in_app_iff; eauto.
      - eapply Forall2_impl_In; [|eauto]; intros.
        unfold idents in H0. apply in_map_iff in H0 as ((?&?&?)&?&?); simpl in *; subst.
        eapply sem_var_restrict; eauto.
        repeat rewrite in_app_iff; eauto.
      - subst. eapply sem_equations_restrict in Heqs; eauto.
        rewrite map_fst_idck in Heqs. assumption.
    Qed.

    Lemma sc_var_inv_intro {prefs2} : forall (n : @node prefs2) H xs,
        Forall2 (sem_var H) (idents (n_in n)) xs ->
        Forall2 (fun xc => sem_clock H (clocks_of xs) (snd xc)) (idck (n_in n)) (map abstract_clock xs) ->
        Forall (sc_var_inv (idck (n_in n ++ n_vars n ++ n_out n)) H (clocks_of xs)) (map fst (n_in n)).
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
  End sc_inv.

  Theorem l_sem_node_clock {prefs} :
    forall (G : @global prefs),
      Forall LCA.node_causal (nodes G) ->
      Ordered_nodes G ->
      wc_global G ->
      sc_nodes G.
  Proof with eauto.
    unfold sc_nodes.
    intros (enums&nodes).
    induction nodes. now inversion 5.
    intros Hcaus Hord Hwc ????? Hsem Hfind Hinv Houtv Hscin. assert (Hsem' := Hsem).
    pose proof (Lord.find_node_not_Is_node_in _ _ _ Hord Hfind) as Hnini.
    inversion_clear Hsem' as [? ? ? ? ? ? Hfind' Hins Houts Heqs Hbk].
    simpl in Hfind. destruct (ident_eq_dec (n_name a) f).
    - rewrite find_node_now in Hfind; auto. inv Hfind.
      rewrite find_node_now in Hfind'; auto. inv Hfind'.
      eapply Forall_sem_equation_global_tl in Heqs; eauto.
      inversion_clear Hord as [|? ? Hord'' Hnneqs Hnn].
      inversion_clear Hwc as [|?? (Hwcn&_) Hwcg].
      inv Hcaus.
      assert (Hwcn':=Hwcn). destruct Hwcn' as (?&?&_&?).

      (* sem_clock H0 -> sem_clock H *)
      eapply sem_clocks_det with (ins:=n_out n0) in Hscin; eauto. 2:rewrite Permutation_app_comm...
      eapply sem_clocks_det...
      clear H Houtv Hinv.

      (* restrict H0 *)
      eapply sem_node_restrict in Heqs as (Hdom&Hins'&Houts'&Heqs'); eauto.
      remember (Env.restrict H0 (idents (n_in n0 ++ n_vars n0 ++ n_out n0))) as H.
      eapply sem_clocks_det with (ins:=n_out n0) in Hscin; eauto. 2:rewrite Permutation_app_comm; eauto.
      eapply sem_clocks_det; eauto.
      clear H0 HeqH Hins Houts.

      (* sem_equation -> sem_equation_anon *)
      subst. eapply sem_equations_sem_equations_anon in Heqs' as (H'&Hr1&_&?); eauto.
      2:repeat rewrite <- app_assoc; apply n_nodup.

      assert (Forall2 (sem_var H') (idents (n_in n0)) xs) as Hins''.
      { eapply Forall2_impl_In; [|eauto]. intros. eapply sem_var_refines; eauto. }
      assert (Forall2 (sem_var H') (idents (n_out n0)) os) as Houts''.
      { eapply Forall2_impl_In; [|eauto]. intros. eapply sem_var_refines; eauto. }
      eapply sem_clocks_det; eauto.

      assert (wc_global (Global enums nodes0)) as Hvars by eauto.
      eapply sc_vars in Hvars; eauto.
      + repeat rewrite map_app, Forall_app in Hvars. destruct Hvars as (_&_&Houts).
        unfold idck, idents in *. rewrite Forall2_map_1, Forall2_map_2. rewrite Forall2_map_1 in Houts'.
        rewrite Forall_map in Houts. eapply Forall2_ignore2' in Houts. 2:eapply Forall2_length in Houts'; eauto.
        eapply Forall2_Forall2 in Houts'; eauto.
        clear - Hr1 Houts'.
        eapply Forall2_impl_In; [|eauto].
        intros (?&?&?) ???(?&?); simpl in *.
        eapply sem_var_refines in H3...
        eapply H2 in H3...
        rewrite in_map_iff. exists (i, (t, c)); split; auto.
        repeat rewrite in_app_iff; auto.
      + eapply sc_var_inv_intro; eauto.
        eapply Forall2_impl_In; [|eauto].
        intros (?&?) ? ? ? ?. eapply sem_clock_refines; eauto.
    - rewrite find_node_other in Hfind; eauto.
      eapply sem_node_cons in Hsem; auto.
      rewrite cons_is_app in Hord.
      inv Hord. inv Hwc. inv Hcaus. eapply IHnodes; eauto.
  Qed.

  Definition sc_var_inv' env H b :=
    Forall (fun '(x, ck) => exists xs, sem_var H x xs /\ sem_clock H b ck (abstract_clock xs)) env.

  Lemma sc_var_inv'_sc_var_inv : forall env H b,
      NoDupMembers env ->
      sc_var_inv' env H b ->
      Forall (sc_var_inv env H b) (map fst env).
  Proof.
    intros * Hndup Hinv'.
    unfold sc_var_inv' in Hinv'.
    rewrite Forall_map.
    eapply Forall_impl_In; [|eauto].
    intros (?&?) Hin (?&Hvar&Hck) ?? Hin' Hvar'.
    eapply NoDupMembers_det in Hin; eauto; subst.
    eapply sem_var_det in Hvar; eauto. rewrite Hvar. assumption.
  Qed.

  Lemma sc_var_inv_sc_var_inv' : forall env H b,
      Forall (fun x => exists v, sem_var H x v) (map fst env) ->
      Forall (sc_var_inv env H b) (map fst env) ->
      sc_var_inv' env H b.
  Proof.
    intros * Hvars Hinv.
    unfold sc_var_inv'.
    rewrite Forall_map in Hinv, Hvars.
    eapply Forall_Forall in Hinv; [|eapply Hvars]. clear Hvars.
    eapply Forall_impl_In; [|eauto].
    intros (?&?) Hin ((v&Hvar)&Hsc).
    exists v. split; eauto.
  Qed.

  Fact sc_var_inv'_refines : forall env H H' b,
      Env.refines eq H H' ->
      sc_var_inv' env H b ->
      sc_var_inv' env H' b.
  Proof.
    intros * Href Hsc.
    unfold sc_var_inv' in *.
    eapply Forall_impl; [|eauto].
    intros (?&?) (?&Hvar&Hck).
    exists x. split.
    - eapply sem_var_refines; eauto.
    - eapply sem_clock_refines; eauto.
  Qed.

  (** We can build an sc_var_inv' once inside the node *)
  Lemma sc_node_sc_var_inv' {prefs} : forall (G : @global prefs) n H xs,
      wc_global G ->
      sc_nodes G ->
      wc_node G n ->
      LCA.node_causal n ->
      Forall2 (sem_var H) (idents (n_in n)) xs ->
      Forall2 (fun xc => sem_clock H (clocks_of xs) (snd xc)) (idck (n_in n)) (map abstract_clock xs) ->
      Forall (sem_equation_anon G H (clocks_of xs)) (n_eqs n) ->
      sc_var_inv' (idck (n_in n ++ n_vars n ++ n_out n)) H (clocks_of xs).
  Proof.
    intros * HwG Hsc Hwcn Hnode Hins Hscin Heqs.

    eapply sc_var_inv_sc_var_inv'.
    - rewrite map_fst_idck.
      assert (Forall (sem_equation G H (clocks_of xs)) (n_eqs n)) as Heqs'.
      { eapply Forall_impl; [|eauto]. intros; eauto using sem_equation_anon_sem_equation. }
      clear Heqs.
      repeat rewrite map_app, Forall_app.
      repeat split.
      + eapply Forall2_ignore2 in Hins.
        eapply Forall_impl; [|eauto]. intros ? (?&?&?); eauto.
      + eapply sem_node_sem_vars in Heqs' as (?&Hvars); eauto. 2:erewrite <- map_app; eapply n_defd.
        eapply Forall2_ignore2 in Hvars.
        eapply Forall_impl; [|eauto]. intros ? (?&?&?); eauto.
      + eapply sem_node_sem_outs in Heqs' as (?&Hvars); eauto. 2:erewrite <- map_app; eapply n_defd.
        eapply Forall2_ignore2 in Hvars.
        eapply Forall_impl; [|eauto]. intros ? (?&?&?); eauto.
    - rewrite map_fst_idck.
      eapply sc_vars; eauto.
      eapply sc_var_inv_intro; eauto.
  Qed.

  Fact wc_exp_Is_free_left {prefs} : forall (G : @global prefs) env e x k,
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
      destruct H4 as [Hex|(?&Hex)]; eauto.
      solve_forall_exists H H6 Hex. solve_forall_exists H1 H8 Hex.
    - (* arrow *)
      destruct H4 as [Hex|[Hex|(?&Hex)]]; eauto.
      solve_forall_exists H H6 Hex. solve_forall_exists H0 H7 Hex. solve_forall_exists H1 H8 Hex.
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

  (** After getting sc_var_inv', we can easily give an alignment lemma for expressions *)
  Lemma sc_exp {prefs} : forall (G : @global prefs) env H b e vs,
      wc_global G ->
      sc_nodes G ->
      NoDupMembers env ->
      sc_var_inv' env H b ->

      wc_exp G env e ->
      sem_exp_anon G H b e vs ->
      Forall2 (sem_clock H b) (clockof e) (map abstract_clock vs).
  Proof.
    intros * HwcG HscG Hnd Hinv Hwc Hsem.
    eapply sc_var_inv'_sc_var_inv in Hinv; eauto.
    assert (forall k, k < numstreams e -> sc_exp_inv G env0 H b e k); intros.
    eapply LCA.exp_causal_ind
      with (P_var:=sc_var_inv env0 H b); eauto.
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
      { eapply sem_exp_anon_sem_exp, sem_exp_numstreams in Hsem; eauto. }
      eapply Forall2_forall2; split.
      + rewrite map_length.
        rewrite length_clockof_numstreams; auto.
      + intros ? ? ? ? ? Hlen Hnth1 Hnth2; subst.
        rewrite length_clockof_numstreams in Hlen.
        specialize (H0 _ Hlen _ Hwc Hsem).
        rewrite nth_indep with (d':=Cbase). 2:rewrite length_clockof_numstreams; auto.
        erewrite map_nth'; eauto. congruence.
  Qed.

  Corollary sc_exps {prefs} : forall (G : @global prefs) H b env es ss,
      wc_global G ->
      sc_nodes G ->
      NoDupMembers env ->
      sc_var_inv' env H b ->

      Forall (wc_exp G env) es ->
      Forall2 (sem_exp_anon G H b) es ss ->
      Forall2 (sem_clock H b) (clocksof es) (map abstract_clock (concat ss)).
  Proof.
    intros * HwcG HscG Hnd Hinv Hwc Hsem.
    assert (length es = length ss) as Hlength by (eapply Forall2_length in Hsem; eauto).
    eapply Forall2_ignore2' in Hwc; eauto.
    eapply Forall2_Forall2 in Hsem; eauto. clear Hwc.
    unfold clocksof. rewrite flat_map_concat_map, Forall2_map_2.
    apply Forall2_concat. rewrite Forall2_map_1.
    eapply Forall2_impl_In; eauto. clear Hsem.
    intros ? ? ? ? (Hwc&Hsem).
    eapply sc_exp in Hsem; eauto.
    rewrite Forall2_map_2 in Hsem; auto.
  Qed.

  Corollary sc_inside' {prefs1 prefs2} :
    forall (G : @global prefs1) H Hi b env es ss bck sub (n : @node prefs2),
      wc_global G ->
      sc_nodes G ->
      NoDupMembers env ->
      sc_var_inv' env H b ->
      Forall (wc_exp G env) es ->
      Forall2 (sem_exp_anon G H b) es ss ->
      wc_env (idck (n_in n)) ->
      Forall2 (WellInstantiated bck sub) (idck (n_in n)) (nclocksof es) ->
      Forall2 (sem_var Hi) (idents (n_in n)) (concat ss) ->
      Forall2 (fun xc : ident * clock => sem_clock Hi (clocks_of (concat ss)) (snd xc)) (idck (n_in n)) (map abstract_clock (concat ss)).
  Proof.
    intros.
    eapply sc_inside; eauto.
    eapply sc_exps; eauto.
  Qed.

  Corollary sc_inside_mask' {prefs1 prefs2} :
    forall (G : @global prefs1) H Hi b env es ss bck sub (n : @node prefs2) k rs,
      wc_global G ->
      sc_nodes G ->
      NoDupMembers env ->
      Forall (wc_exp G env) es ->
      Forall2 (sem_exp_anon G H b) es ss ->
      sc_var_inv' env H b ->
      wc_env (idck (n_in n)) ->
      Forall2 (WellInstantiated bck sub) (idck (n_in n)) (nclocksof es) ->
      Forall2 (sem_var Hi) (idents (n_in n)) (map (mask k rs) (concat ss)) ->
      Forall2 (fun xc : ident * clock => sem_clock Hi (clocks_of (map (mask k rs) (concat ss))) (snd xc)) (idck (n_in n)) (map abstract_clock (map (mask k rs) (concat ss))).
  Proof.
    intros.
    eapply sc_inside_mask; eauto.
    eapply sc_exps; eauto.
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
  Section sc_ref.
    Context {pref1 pref2 : PS.t}.

    (** Functional equivalence for nodes *)
    Definition node_sc_refines (G : @global pref1) (G' : @global pref2) f : Prop :=
      (forall ins outs, (sem_clock_inputs G f ins /\ sem_node G f ins outs) ->
                   (sem_clock_inputs G' f ins /\ sem_node G' f ins outs)).

    Definition global_sc_refines (G : @global pref1) (G' : @global pref2) : Prop :=
      forall f, node_sc_refines G G' f.

    Ltac ndup_l H :=
      rewrite app_assoc in H;
      apply NoDupMembers_app_l in H; auto.
    Ltac ndup_r H :=
      rewrite Permutation_swap in H;
      apply NoDupMembers_app_r in H; auto.

    Hint Resolve NoDupMembers_fresh_in_anon_in NoDupMembers_fresh_in' NoDupMembers_anon_in' nth_In.
    Hint Constructors sem_exp_anon.
    Fact sc_ref_sem_exp : forall G G' H b vars e vs,
        global_sc_refines G G' ->
        wc_global G ->
        sc_nodes G ->
        NoDupMembers vars ->
        wc_exp G vars e ->
        sc_var_inv' vars H b ->
        sem_exp_anon G H b e vs ->
        sem_exp_anon G' H b e vs.
    Proof with eauto.
      induction e using exp_ind2; intros * Heq HwcG Hsc Hvars Hwc Hinv Hsem;
        inv Hwc; inv Hsem...
      - (* fby *)
        econstructor...
        + repeat rewrite_Forall_forall... eapply H0...
        + repeat rewrite_Forall_forall... eapply H1...
        + repeat rewrite_Forall_forall... eapply H2...
      - (* arrow *)
        econstructor...
        + repeat rewrite_Forall_forall... eapply H0...
        + repeat rewrite_Forall_forall... eapply H1...
        + repeat rewrite_Forall_forall... eapply H2...
      - (* when *)
        econstructor...
        repeat rewrite_Forall_forall... eapply H0...
      - (* merge *)
        econstructor...
        do 2 (eapply Forall2_impl_In; [|eauto]; intros).
        do 2 (eapply Forall_forall in H0; eauto).
        do 2 (eapply Forall_forall in H6; eauto).
      - (* case *)
        econstructor...
        + clear H21. do 2 (eapply Forall2_impl_In; [|eauto]; intros; subst).
          do 2 (eapply Forall_forall in H0; eauto; simpl in H0).
          eapply Forall_forall in H9; eauto.
        + eapply Forall2_impl_In; [|eauto]; intros.
          eapply Forall_forall in H1; eauto.
          eapply H1; eauto. eapply Forall_forall; eauto.
      - (* app *)
        econstructor...
        + repeat rewrite_Forall_forall... eapply H0...
        + repeat rewrite_Forall_forall... eapply H1...
        + intros k. specialize (H19 k).
          specialize (Heq f (map (mask k bs) (concat ss)) (map (mask k bs) vs)).
          eapply Heq. split; auto.
          inv H19. rewrite H3 in H8; inv H8.
          exists H2. exists n.
          repeat split; auto.
          eapply sc_inside_mask'. 1-3,5-12:eauto. 2:eauto.
          eapply wc_find_node in H3 as [? [? _]]; eauto.
    Qed.

    Fact sc_ref_sem_equation : forall G G' H b vars eq,
        global_sc_refines G G' ->
        wc_global G ->
        sc_nodes G ->
        NoDupMembers vars ->
        wc_equation G vars eq ->
        sc_var_inv' vars H b ->
        sem_equation_anon G H b eq ->
        sem_equation_anon G' H b eq.
    Proof.
      intros G G' H b vars [xs es] Heq HwcG Hsc Hndup [Hwc _] Hinv Hsem.
      inv Hsem.
      econstructor; eauto.
      repeat rewrite_Forall_forall; eauto.
      eapply sc_ref_sem_exp; eauto.
    Qed.

    Fact global_sc_ref_nil : forall enums,
      global_sc_refines (Global enums []) (Global enums []).
    Proof.
      intros * f ins outs Hsem. destruct Hsem as (_&Hsem).
      inv Hsem. unfold find_node in H0; simpl in H0; inv H0.
    Qed.

    Fact global_sc_ref_cons : forall enums nds nds' n n' f,
        Ordered_nodes (Global enums (n::nds)) ->
        Ordered_nodes (Global enums (n'::nds')) ->
        n_name n = f ->
        n_name n' = f ->
        global_sc_refines (Global enums nds) (Global enums nds') ->
        node_sc_refines (Global enums (n::nds)) (Global enums (n'::nds')) f ->
        global_sc_refines (Global enums (n::nds)) (Global enums (n'::nds')).
    Proof with eauto.
      intros * Hord1 Hord2 Hname1 Hname2 Hglob Hnode f0 ins outs Hsem.
      inv Hsem.
      simpl in H0.
      destruct (ident_eq_dec (n_name n) f0); subst.
      + specialize (Hnode ins outs).
        eapply Hnode.
        econstructor; eauto.
      + rewrite <- sem_clock_inputs_cons... rewrite <- sem_node_cons_iff...
        specialize (Hglob f0 ins outs). apply Hglob.
        rewrite sem_clock_inputs_cons... rewrite sem_node_cons_iff...
    Qed.

  End sc_ref.

  (** ** Execution of a node with absent inputs *)

  Section sem_node_absent.
    Context {prefs : PS.t}.

    Lemma Forall2_sem_exp_absent: forall (f : list (Stream svalue) -> list (Stream svalue)) (G : @global prefs) H b es ss,
        Forall2 (fun e vs => sem_exp G H b e (f vs)) es ss ->
        Forall2 (sem_exp G H b) es (map f ss).
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

    Lemma clocks_of_false: forall ss,
      clocks_of (map (fun _ : Stream svalue => Streams.const absent) ss) ≡ Streams.const false.
    Proof.
      intros *.
      eapply ntheq_eqst. intros n.
      rewrite clocks_of_nth, const_nth.
      induction ss; simpl; auto.
      rewrite const_nth; simpl; auto.
    Qed.

    Lemma mask_absent: forall k rs,
        mask k rs (Streams.const absent) ≡ Streams.const absent.
    Proof.
      intros *.
      eapply ntheq_eqst. intros n.
      rewrite mask_nth. rewrite const_nth.
      destruct (_ =? k); auto.
    Qed.

    Lemma fby_absent: forall rs,
      fby (Streams.const absent) (Streams.const absent) rs (Streams.const absent).
    Proof.
      unfold fby.
      cofix CoFix. intros rs.
      rewrite CommonStreams.const_Cons. unfold_Stv rs; constructor; auto.
    Qed.

    Lemma arrow_absent: forall rs,
      arrow (Streams.const absent) (Streams.const absent) rs (Streams.const absent).
    Proof.
      unfold arrow.
      cofix CoFix. intros rs.
      rewrite CommonStreams.const_Cons. unfold_Stv rs; constructor; auto.
    Qed.

    Lemma sem_node_absent:
      forall (G : @global prefs) f xs ys,
        sem_node G f xs ys ->
        sem_node G f (map (fun _ => Streams.const absent) xs) (map (fun _ => Streams.const absent) ys).
    Proof.
      intros * Sem.
      induction Sem using sem_node_ind2
        with (P_exp := (fun H _ e vs => sem_exp G (Env.map (fun _ => Streams.const absent) H)
                                             (Streams.const false) e (List.map (fun _ => Streams.const absent) vs)))
             (P_equation := (fun H _ eq => sem_equation G (Env.map (fun _ => Streams.const absent) H) (Streams.const false) eq));
        simpl in *.
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
        econstructor. 3:eapply Forall2_map_2 with (f:=fun _ => Streams.const absent); eauto.
        1-3:eauto using bools_ofs_absent.
        repeat rewrite <-concat_map. rewrite Forall3_map_1, Forall3_map_2, Forall3_map_3.
        eapply Forall3_impl_In; [|eauto]. intros * _ _ _ _. apply fby_absent.
      - (* Earrow *)
        econstructor. 3:eapply Forall2_map_2 with (f:=fun _ => Streams.const absent); eauto.
        1-3:eauto using bools_ofs_absent.
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
        + clear H1.
          erewrite Forall2_map_2.
          do 2 (eapply Forall2_impl_In; [|eauto]; intros); eauto.
        + replace (map (@concat _) (map (map (map (fun _ => Streams.const absent))) vs))
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
        + clear H3.
          erewrite Forall2_map_2.
          do 2 (eapply Forall2_impl_In; [|eauto]; intros; subst); eauto.
        + clear H2. rewrite Forall2_map_2.
          eapply Forall2_impl_In; [|eauto]; intros; simpl in *.
          erewrite Forall2_map_1, Forall2_map_2. eapply Forall2_impl_In; [|eauto]; intros.
          eapply map_st_EqSt with (y:=fun _ => Streams.const absent); eauto.
          intros; reflexivity.
        + erewrite Forall2_map_2.
          eapply Forall2_impl_In; [|eauto]; intros. simpl in *; eauto.
        + replace (map (@concat _) (map (map (map (fun _ => Streams.const absent))) vs))
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
        econstructor. 2:eapply Forall2_map_2 with (f0:=fun _ => Streams.const absent); eauto.
        1,2:eauto using bools_ofs_absent.
        erewrite <-concat_map; eauto.
        intros k. specialize (H5 k) as (?&SemN).
        repeat rewrite map_map in *.
        eapply mod_sem_node_morph; eauto.
        1,2:eapply map_st_EqSt_Proper. 2,4:reflexivity.
        1,2:intros * Eq; symmetry; apply mask_absent.
      - (* Equation *)
        econstructor; eauto.
        rewrite <-concat_map, Forall2_map_2.
        eapply Forall2_impl_In; eauto.
      - (* Node *)
        econstructor. 5:reflexivity. 1-4:eauto; subst.
        1,2:(rewrite Forall2_map_2; eapply Forall2_impl_In; [|eauto];
             intros; eapply sem_var_absent; eauto).
        eapply Forall_impl; [|eauto].
        intros ? Sem; simpl in *.
        rewrite clocks_of_false; auto.
    Qed.

    Lemma sem_var_instant_absent: forall H x v,
        sem_var_instant H x v ->
        sem_var_instant (Env.map (fun _ => absent) H) x absent.
    Proof.
      intros * Var. unfold sem_var_instant in *.
      rewrite Env.Props.P.F.map_o, Var; auto.
    Qed.
    Hint Resolve sem_var_instant_absent.

    Lemma sem_clock_false: forall H ck b b',
        IStr.sem_clock b H ck b' ->
        IStr.sem_clock (fun _ => false) (fun n => Env.map (fun _ => absent) (H n)) ck (fun _ => false).
    Proof.
      intros * Sem n. specialize (Sem n).
      revert Sem. generalize (b n) (b' n). clear b b'.
      induction ck; intros * Sem; inv Sem; eauto using sem_clock_instant.
    Qed.

    Lemma sem_clock_inputs_false: forall (G : @global prefs) f xs,
      sem_clock_inputs G f xs ->
      sem_clock_inputs G f (map (fun _ => Streams.const absent) xs).
    Proof.
      intros * (H&n&Find&Sem&Ck).
      exists (Env.map (fun _ => Streams.const absent) H). exists n.
      repeat split; auto.
      - rewrite Forall2_map_2. eapply Forall2_impl_In; eauto.
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
       (IStr : INDEXEDSTREAMS Ids Op OpAux Cks)
       (Sem : LSEMANTICS Ids Op OpAux Cks Syn Lord CStr)
<: LCLOCKSEMANTICS Ids Op OpAux Cks Syn Clo LCA Lord CStr IStr Sem.
  Include LCLOCKSEMANTICS Ids Op OpAux Cks Syn Clo LCA Lord CStr IStr Sem.
End LClockSemanticsFun.
