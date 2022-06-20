From Coq Require Import List.
Import List.ListNotations.
Open Scope list_scope.

From Coq Require Import Recdef.
From Velus Require Import Common.
From Velus Require Import CommonProgram.
From Velus Require Import Operators.
From Velus Require Import Clocks.
From Velus Require Import Environment.
From Velus Require Import CoreExpr.CESyntax.
From Velus Require Import CoreExpr.CEIsFree.
From Velus Require Import NLustre.NLSyntax.
From Velus Require Import NLustre.IsFree.
From Velus Require Import NLustre.Memories.
From Velus Require Import NLustre.IsDefined.

(** Remove dead code in an NLustre program *)

Module Type DCE
       (Import Ids   : IDS)
       (Import Op    : OPERATORS)
       (Import OpAux : OPERATORS_AUX   Ids Op)
       (Import Cks   : CLOCKS      Ids Op OpAux)
       (Import CESyn : CESYNTAX    Ids Op OpAux Cks)
       (Import CEF   : CEISFREE    Ids Op OpAux Cks CESyn)
       (Import Syn   : NLSYNTAX    Ids Op OpAux Cks CESyn)
       (Import Free  : ISFREE      Ids Op OpAux Cks CESyn Syn CEF)
       (Import Mem   : MEMORIES    Ids Op OpAux Cks CESyn Syn)
       (Import Def   : ISDEFINED   Ids Op OpAux Cks CESyn Syn Mem).

  (** *** Build a dependency graph *)

  Definition free_graph (eqs : list equation) :=
    fold_right (fun eq gr =>
                  let defs := defined_eq PS.empty eq in
                  let frees := free_in_equation eq PS.empty in
                  let fdefs := PS.union defs frees in
                  PS.fold (fun x => Env.add x fdefs) defs gr)
               (Env.empty _) eqs.

  Fact fold_In : forall defs (frees : PS.t) gr x,
      Env.In x (PS.fold (fun x => Env.add x frees) defs gr) <->
      PS.In x defs \/ Env.In x gr.
  Proof.
    intros *.
    apply PSP.fold_rec.
    - intros * Hemp. split; auto.
      intros [Hin|]; subst; auto.
      apply Hemp in Hin as [].
    - intros * Hin Hnin Hadd Hrec.
      rewrite Env.Props.P.F.add_in_iff. split; intros [|]; subst.
      + left. apply Hadd; auto.
      + apply Hrec in H as [|]; auto.
        left. apply Hadd; auto.
      + apply Hadd in H as [|]; auto.
        right. apply Hrec; auto.
      + right. apply Hrec; auto.
  Qed.

  Lemma free_graph_In : forall x eqs,
      Env.In x (free_graph eqs) <-> Is_defined_in x eqs.
  Proof.
    unfold free_graph.
    split.
    - induction eqs; intros * Hin; simpl in *.
      + apply Env.Props.P.F.empty_in_iff in Hin; inv Hin.
      + apply fold_In in Hin as [|].
        * left. apply Is_defined_in_eqP, PSF.mem_iff; auto.
        * right. apply IHeqs. auto.
    - induction eqs; intros * Hin; simpl in *. inv Hin.
      rewrite fold_In.
      inv Hin; auto.
      left. apply PSF.mem_iff, Is_defined_in_eqP; auto.
  Qed.

  Fact find_fold_spec : forall defs (frees : PS.t) gr x ps,
      (forall x, PS.In x defs -> ~Env.In x gr) ->
      Env.find x (PS.fold (fun x => Env.add x frees) defs gr) = Some ps <->
      (PS.In x defs /\ ps = frees) \/ Env.find x gr = Some ps.
  Proof.
    intros * Hnd.
    apply PSP.fold_rec.
    - intros * Hemp. split; auto.
      intros [(?&?)|]; subst; auto.
      apply Hemp in H as [].
    - intros * Hin Hnin Hadd Hrec.
      rewrite Env.gsspec. destruct (Env.Props.P.F.eq_dec x x0); subst; split.
      + intros Heq. inv Heq. left. split; auto.
        apply Hadd; auto.
      + intros [(?&?)|Hfind]; subst; auto. exfalso.
        eapply Hnd; eauto. econstructor; eauto.
      + intros Hfind. apply Hrec in Hfind as [(?&?)|]; subst; auto.
        left; split; auto.
        apply Hadd; auto.
      + intros [(Hin'&?)|Hfind]; subst; auto.
        * apply Hrec. left; split; auto.
          apply Hadd in Hin' as [|]; subst; auto. congruence.
        * apply Hrec; auto.
  Qed.

  Lemma free_graph_spec : forall eqs,
      NoDup (vars_defined eqs) ->
      (forall x y, (exists ps, Env.find x (free_graph eqs) = Some ps /\ PS.In y ps) <->
              Exists (fun eq => Is_defined_in_eq x eq /\ (Is_free_in_eq y eq \/ Is_defined_in_eq y eq)) eqs).
  Proof.
    unfold free_graph.
    intros * Hnd; split; revert eqs Hnd.
    - induction eqs; intros * Hnd * (?&Hmaps&Hin); simpl in *; subst.
      + apply Env.Props.P.F.empty_mapsto_iff in Hmaps. inv Hmaps.
      + rewrite find_fold_spec in Hmaps.
        2:{ clear - Hnd. intros ? Hin1 Hin2. rewrite free_graph_In in Hin2.
            apply Is_defined_in_eqP, Is_defined_in_var_defined in Hin1.
            apply Is_defined_in_vars_defined in Hin2.
            eapply NoDup_app_In in Hnd; eauto. }
        destruct Hmaps as [(Hdef&?)|]; subst.
        * left. rewrite PSF.union_iff, free_in_equation_spec' in Hin.
          apply Is_defined_in_eqP in Hdef. destruct Hin as [Hin|]; auto.
          apply Is_defined_in_eqP in Hin; auto.
        * right. apply IHeqs; eauto using NoDup_app_r.
    - induction eqs; intros * Hnd * Hex; simpl in *. inv Hex.
      assert (forall x, PS.In x (defined_eq PS.empty a) ->
                   ~Env.In x
                    (fold_right
                       (fun eq gr =>
                          PS.fold (fun x1 : positive => Env.add x1 (PS.union (defined_eq PS.empty eq) (free_in_equation eq PS.empty)))
                                  (defined_eq PS.empty eq) gr) (Env.empty PS.t) eqs)) as Hnd'.
      { clear - Hnd. intros ? Hin1 Hin2. rewrite free_graph_In in Hin2.
        apply Is_defined_in_eqP, Is_defined_in_var_defined in Hin1.
        apply Is_defined_in_vars_defined in Hin2.
        eapply NoDup_app_In in Hnd; eauto. }
      inv Hex.
      + clear IHeqs. destruct H0 as (Hdef&Hfree).
        exists (PS.union (defined_eq PS.empty a) (free_in_equation a PS.empty)). rewrite find_fold_spec; auto.
        split; [left; split; auto; apply Is_defined_in_eqP; auto|].
        rewrite PSF.union_iff, free_in_equation_spec'.
        destruct Hfree; auto.
        left. apply Is_defined_in_eqP; auto.
      + apply IHeqs in H0 as (ps&?&?); eauto using NoDup_app_r.
        exists ps. rewrite find_fold_spec; auto.
  Qed.

  (** *** Calculate the set of used variables *)

  Section compute_used.

    Variable (gr : Env.t PS.t) (* (n : nat) *).

    Definition handle_one (whites greys : PS.t) (x : ident) :=
      let ps := or_default PS.empty (Env.find x gr) in
      PS.fold (fun x '(whites, greys) => (PS.remove x whites, if PS.mem x whites then PS.add x greys else greys))
              ps (PS.remove x whites, PS.remove x greys).

    Function compute_unused whgs {measure (fun '(wh, gs) => (PS.cardinal wh + PS.cardinal gs)) whgs} :=
      match PS.choose (snd whgs) with
      | None => (fst whgs)
      | Some x =>
        let '(wh, gs) := handle_one (fst whgs) (snd whgs) x in
        compute_unused (wh, gs)
      end.
    Proof.
      intros * Hchoose * Hhandle.
      destruct whgs.
      unfold handle_one in *.
      apply PS.choose_spec1 in Hchoose.
      revert wh gs Hhandle.
      apply PSE.MP.fold_rec.
      - intros * _ * Heq. inv Heq.
        erewrite <-PSP.remove_cardinal_1 with (s:=t0); eauto.
        destruct (PSdec.MSetDecideAuxiliary.dec_In x t).
        + erewrite <-PSP.remove_cardinal_1 with (s:=t); eauto. lia.
        + erewrite <-PSP.remove_cardinal_2 with (s:=t); eauto. lia.
      - intros ? (?&?) * _ Hnin Hadd Hrec * Heq. inv Heq.
        eapply Nat.le_lt_trans; [|eauto].
        destruct (PS.mem x0 t1) eqn:Hmem.
        + erewrite <-PSP.remove_cardinal_1 with (s:=t1); eauto.
          destruct (PSdec.MSetDecideAuxiliary.dec_In x0 t2).
          * rewrite PSP.add_cardinal_1; auto. lia.
          * rewrite PSP.add_cardinal_2; auto. lia.
        + erewrite <-PSP.remove_cardinal_2 with (s:=t1); eauto using PSE.mem_4.
    Defined.

    Lemma handle_one_spec : forall wh1 gs1 x wh2 gs2 ps,
        Env.find x gr = Some ps ->
        ~PS.In x wh1 ->
        handle_one wh1 gs1 x = (wh2, gs2) ->
        (forall y, PS.In y wh2 <-> PS.In y wh1 /\ y <> x /\ ~PS.In y ps) /\
        (forall y, PS.In y gs2 <-> (PS.In y gs1 /\ y <> x) \/ (PS.In y wh1 /\ PS.In y ps)).
    Proof.
      unfold handle_one.
      intros * Hfind Hninx. rewrite Hfind in *; simpl in *; clear Hfind.
      revert wh2 gs2. apply PSP.fold_rec.
      - intros ? Hempty * Heq. inv Heq. do 2 split.
        + intros Hin.
          repeat split; eauto using PSF.remove_3.
          * intro contra; subst.
            apply PSF.remove_1 in Hin; auto.
        + intros (?&?&?). apply PSF.remove_2; auto.
        + intros Hin.
          left. repeat split; eauto using PSF.remove_3.
          intro contra; subst.
          apply PSF.remove_1 in Hin; auto.
        + intros [(?&?)|(?&?)]; eauto using PSF.remove_2.
          exfalso. eapply Hempty; eauto.
      - intros ? (wh2&gs2) * Hin Hnin Hadd Hrec * Heq. inv Heq.
        specialize (Hrec _ _ eq_refl) as (Hrec1&Hrec2). do 2 split.
        + intros Hin1. specialize (Hrec1 y) as ((Hin'&?&Hnin')&_); eauto using PSF.remove_3.
          repeat split; auto.
          contradict Hnin'. apply Hadd in Hnin' as [|]; auto; subst.
          exfalso. apply PSF.remove_1 in Hin1; auto.
        + intros (Hin1&Heq&Hnin1).
          apply PSF.remove_2; auto.
          * intro contra; subst. eapply Hnin1, Hadd; auto.
          * apply Hrec1. repeat split; auto.
            contradict Hnin1. apply Hadd; auto.
        + intros Hin1.
          destruct (PSdec.MSetDecideAuxiliary.dec_In y gs2).
          * specialize (Hrec2 y) as ([(?&?)|(?&Hnin1)]&_); eauto using PSF.remove_3.
            right. split; auto.
            apply Hadd; auto.
          * destruct (PS.mem x0 wh2) eqn:Hmem; try congruence.
            apply PSF.add_iff in Hin1 as [|]; try congruence; subst.
            apply Hrec1 in Hmem as (?&?&Hnin1).
            right. split; auto.
            apply Hadd; auto.
        + intros H.
          destruct (ident_eq_dec y x0)(* , (PS.mem x0 t) *); subst.
          2:{ assert (PS.In y gs2) as Hin'. 2:destruct (PS.mem _ _); auto using PSF.add_2.
              apply Hrec2. destruct H as [|(?&Hin')]; auto.
              right. split; auto.
              apply Hadd in Hin' as [|]; auto. congruence. }
          destruct H as [(Hin1&Hneq)|(Hin1&Hin2)].
          * assert (PS.In x0 gs2) as Hin'. 2:destruct (PS.mem _ _); auto using PSF.add_2.
            apply Hrec2; auto.
          * destruct (ident_eq_dec x0 x); subst.
            -- contradiction.
            -- assert (PS.In x0 wh2) as Hin'.
               { apply Hrec1. repeat split; auto. }
              rewrite Hin'. apply PSF.add_1; auto.
    Qed.

    Lemma compute_unused_stable : forall whgs1 wh2 x,
        (forall x, PS.In x (fst whgs1) \/ PS.In x (snd whgs1) -> Env.In x gr) ->
        (forall x, PS.In x (fst whgs1) -> ~PS.In x (snd whgs1)) ->
        compute_unused whgs1 = wh2 ->
        PS.In x wh2 ->
        PS.In x (fst whgs1) /\
        (forall y ps, PS.In y (fst whgs1) \/ PS.In y (snd whgs1) -> Env.find y gr = Some ps -> PS.In x ps -> PS.In y wh2). (* Hum *)
    Proof.
      intros * Hgr Hnd. revert wh2.
      functional induction (compute_unused whgs1); destruct whgs as (wh1&gs1); simpl in *.
      - intros * ? Hin; subst.
        split; auto.
        intros ?? [|]; auto. exfalso.
        apply PS.choose_spec2 in e. apply e in H; auto.
        (* intros ?? Hfind Hin'. edestruct Hgr; [econstructor; eauto| |]; auto. *)
        (* exfalso. apply CommonPS.PS.choose_spec2 in e. apply e in H; auto. *)
      - intros ? Hcomp Hin.
        assert (Env.In x0 gr) as (ps&Hfind).
        { apply Hgr. right; auto using PSF.choose_1. }
        unfold Env.MapsTo in Hfind.
        assert (~ PS.In x0 wh1) as Hninx.
        { intro contra. eapply Hnd; eauto using PS.choose_spec1. }
        eapply handle_one_spec in e0 as (Hspec1&Hspec2); eauto.
        assert (forall x, PS.In x wh -> ~ PS.In x gs) as Hnd'.
        { intros ? Hin1 Hin2. apply Hspec1 in Hin1 as (Hin1&?&?).
          apply Hspec2 in Hin2 as [(?&?)|(?&?)]; try congruence.
          eapply Hnd; eauto. }
        eapply IHt in Hcomp as (Hrec1&Hrec2); eauto.
        2:{ intros ? [?|Hin']; apply Hgr.
            - left. apply Hspec1; auto.
            - apply Hspec2 in Hin' as [(?&?)|(?&?)]; auto. }
        split. apply Hspec1; auto.
        intros ?? Hin1 Hfind' Hin'.
        destruct (ident_eq_dec x y); subst; auto.
        destruct (ident_eq_dec y x0); subst.
        { destruct Hin1 as [|Hin1]; try congruence.
          exfalso.
          rewrite Hfind' in Hfind; inv Hfind.
          apply Hspec1 in Hrec1 as (?&?&?). congruence. }
        assert (PS.In y wh \/ PS.In y gs); eauto.
        { destruct Hin1 as [Hin1|Hin1].
          - destruct (PSE.MP.Dec.MSetDecideAuxiliary.dec_In y ps) as [Hps|Hps].
            + right. apply Hspec2; auto.
            + left. apply Hspec1; repeat split; auto.
          - right. apply Hspec2; auto.
        }
    Qed.

  End compute_used.

  Definition dce_eqs (outs : PS.t) (vars : list (ident * (type * clock))) (eqs : list equation) :=
    let gr := free_graph eqs in
    let unused := compute_unused gr (PSP.of_list (map fst vars), outs) in
    (List.filter (fun '(x, _) => negb (PS.mem x unused)) vars,
     List.filter (fun eq => PS.for_all (fun x => negb (PS.mem x unused)) (defined_eq PS.empty eq)) eqs).

  Lemma dce_eqs_defined : forall outs vars eqs vars' eqs',
      NoDup (vars_defined eqs) ->
      (forall x, InMembers x vars -> ~PS.In x outs) ->
      (forall x, Is_defined_in x eqs <-> InMembers x vars \/ PS.In x outs) ->
      dce_eqs outs vars eqs = (vars', eqs') ->
      (forall x, Is_defined_in x eqs' <-> InMembers x vars' \/ PS.In x outs).
  Proof.
    unfold dce_eqs.
    intros * Hvd Hnd Hdef Hdce. inv Hdce.
    unfold Is_defined_in in *.
    intros x. rewrite filter_InMembers, Exists_exists. setoid_rewrite filter_In.
    setoid_rewrite Exists_exists in Hdef.
    split.
    - intros (?&(Hineqs&Hf)&Hisdef).
      edestruct Hdef as ([Hin|]&_); eauto.
      apply InMembers_In in Hin as (?&Hin).
      left. repeat esplit; eauto.
      apply PS.for_all_spec in Hf. 2:{ intros ?? Heq; inv Heq; auto. }
      apply Is_defined_in_eqP, Hf in Hisdef.
      auto.
    - intros Hin.
      assert (~PS.In x (compute_unused (free_graph eqs) (PSP.of_list (map fst vars), outs))) as Hnin.
      { intro Hin2.
        assert (Hcomp:=Hin2). eapply compute_unused_stable in Hcomp. 4:reflexivity. 1-3:simpl in *.
        - destruct Hcomp as (Hin1&_).
          apply In_of_list_InMembers in Hin1.
          destruct Hin as [((?&?)&_&Hneg)|Hin].
          + apply Bool.negb_true_iff, PSP.FM.not_mem_iff in Hneg.
            contradiction.
          + eapply Hnd; eauto.
        - intros ? Hin1.
          apply free_graph_In. apply Exists_exists, Hdef.
          destruct Hin1; auto. left. apply In_of_list_InMembers; auto.
        - intros ??. apply Hnd, In_of_list_InMembers; auto.
      }
      edestruct Hdef as (_&(?&?&?)).
      + destruct Hin as [((?&?)&?&?)|]; eauto using In_InMembers.
      + repeat esplit; eauto.
        eapply PS.for_all_spec. intros ?? Heq; inv Heq; auto.
        intros ? Hisdef. apply Is_defined_in_eqP in Hisdef.
        apply Bool.negb_true_iff, PSP.FM.not_mem_iff.
        intros Hin'.
        assert (Hcomp:=Hin'). eapply compute_unused_stable in Hcomp. 4:reflexivity. 1-3:simpl in *.
        * destruct Hcomp as (Hin1&Hin2).
          assert (exists ps, Env.find x (free_graph eqs) = Some ps /\ PS.In x1 ps) as (?&?&?).
          { eapply free_graph_spec; eauto.
            eapply Exists_exists; eauto.
          }
          eapply Hnin in Hin2; eauto.
          rewrite In_of_list_InMembers. eapply Hdef; eauto.
        * intros ? Hin1.
          apply free_graph_In. apply Exists_exists, Hdef.
          destruct Hin1; auto. left. apply In_of_list_InMembers; auto.
        * intros ??. apply Hnd, In_of_list_InMembers; auto.
  Qed.

  Lemma dce_eqs_stable : forall (ins vars outs : list (ident * (type * clock))) eqs vars' eqs',
      NoDup (vars_defined eqs) ->
      (forall x, InMembers x vars -> ~InMembers x outs) ->
      (forall x, InMembers x (vars ++ outs) <-> Is_defined_in x eqs) ->
      Forall (fun eq => exists x, Is_defined_in_eq x eq) eqs ->
      (forall x, Exists (fun eq => Is_defined_in_eq x eq \/ Is_free_in_eq x eq) eqs -> InMembers x (ins ++ vars ++ outs)) ->
      dce_eqs (PSP.of_list (map fst outs)) vars eqs = (vars', eqs') ->
      (forall x, Exists (fun eq => Is_defined_in_eq x eq \/ Is_free_in_eq x eq) eqs' -> InMembers x (ins ++ vars' ++ outs)).
  Proof.
    unfold dce_eqs.
    intros * Hnd1 Hnd2 Hdef Hvd Hex1 Hdce * Hex. inv Hdce.
    apply Exists_exists in Hex as (?&Hin&Hex). apply filter_In in Hin as (Hin&Hf).
    apply PS.for_all_spec in Hf. 2:{ intros ?? Heq; inv Heq; auto. }
    specialize (Hex1 x). rewrite Exists_exists in Hex1.
    repeat rewrite InMembers_app in *. destruct Hex1 as [|[Hin'|]]; eauto.
    right; left.
    eapply InMembers_In in Hin' as (?&Hin').
    eapply filter_InMembers. repeat esplit; eauto.
    destruct Hex as [Hex|Hex].
    - apply Is_defined_in_eqP, Hf in Hex; auto.
    - apply Bool.negb_true_iff, PSF.not_mem_iff.
      intros Hcomp.
      eapply compute_unused_stable in Hcomp as (Hcomp1&Hcomp2). 4:reflexivity. 1-3:simpl in *.
      + eapply Forall_forall in Hvd as (y&Hvd); eauto.
        assert (exists ps : PS.t, Env.find y (free_graph eqs) = Some ps /\ PS.In x ps) as (?&Hfind&Hps).
        { eapply free_graph_spec; eauto.
          eapply Exists_exists; eauto.
        }
        assert (Hvd':=Hvd). apply Is_defined_in_eqP, Hf, Bool.negb_true_iff, PSF.not_mem_iff in Hvd.
        eapply Hvd, Hcomp2; eauto. rewrite 2 In_of_list_InMembers; eauto using In_InMembers.
        rewrite <-InMembers_app. eapply Hdef, Exists_exists; eauto.
      + intros ? Hin1.
        apply free_graph_In. apply Hdef.
        rewrite 2 In_of_list_InMembers in Hin1.
        rewrite InMembers_app; auto.
      + intros ?. rewrite 2 In_of_list_InMembers; auto.
  Qed.

  (** ** Transformation of the node and global *)

  Import Permutation.

  Definition dce_eqs' (outs vars : list (ident * (type * clock))) eqs :
    { res | dce_eqs (PSP.of_list (map fst outs)) vars eqs = res }.
  Proof.
    econstructor. reflexivity.
  Defined.

  Fact vars_defined_filter_In : forall p eqs x,
      In x (vars_defined (filter p eqs)) ->
      In x (vars_defined eqs).
  Proof.
    induction eqs; intros * Hin; simpl in *; auto.
    destruct (p a); simpl in *; eauto with datatypes.
    apply in_app_iff in Hin as [|]; eauto with datatypes.
  Qed.

  Corollary vars_defined_filter_NoDup : forall p eqs,
      NoDup (vars_defined eqs) ->
      NoDup (vars_defined (filter p eqs)).
  Proof.
    induction eqs; intros * Hnd; simpl in *; auto.
    destruct (p a); simpl; eauto using NoDup_app_r.
    eapply NoDup_app'; eauto using NoDup_app_l, NoDup_app_r.
    eapply Forall_forall; intros ? Hin1 Hin2.
    eapply NoDup_app_In in Hnd; eauto.
    eapply Hnd, vars_defined_filter_In; eauto.
  Qed.

  Fact dce_NoDupMembers_filter {A} : forall (ins vars outs : list (ident * A)) p,
      NoDupMembers (ins ++ vars ++ outs) ->
      NoDupMembers (ins ++ filter p vars ++ outs).
  Proof.
    intros * Hnd.
    repeat apply NoDupMembers_app; eauto using NoDupMembers_filter, NoDupMembers_app_l, NoDupMembers_app_r.
    - intros ? Hin1 Hin2. eapply filter_InMembers' in Hin1.
      eapply NoDupMembers_app_r, NoDupMembers_app_InMembers in Hnd; eauto.
    - intros ? Hin1 Hin2.
      eapply NoDupMembers_app_InMembers in Hnd; eauto.
      rewrite InMembers_app in Hin2, Hnd. apply not_or' in Hnd as (?&?).
      destruct Hin2 as [Hin2|]; eauto using filter_InMembers'.
  Qed.

  Fact dce_vars_defined : forall eqs (vars outs : list (ident * (type * clock))) vars' eqs',
      NoDupMembers (vars ++ outs) ->
      Permutation (vars_defined eqs) (map fst (vars ++ outs)) ->
      dce_eqs (PSP.of_list (map fst outs)) vars eqs = (vars', eqs') ->
      Permutation (vars_defined eqs') (map fst (vars' ++ outs)).
  Proof.
    intros * Hnd Hperm Hdce. inv Hdce.
    apply NoDup_Permutation.
    - apply vars_defined_filter_NoDup. now rewrite Hperm, <-fst_NoDupMembers.
    - apply fst_NoDupMembers.
      apply NoDupMembers_app; eauto using NoDupMembers_app_l, NoDupMembers_app_r, NoDupMembers_filter.
      intros ? Hinm1 Hinm2.
      eapply filter_InMembers' in Hinm1. eapply NoDupMembers_app_InMembers in Hnd; eauto.
    - intros ?. rewrite <-Is_defined_in_vars_defined, dce_eqs_defined.
      5:unfold dce_eqs; reflexivity.
      + rewrite map_app, in_app_iff, In_of_list_InMembers, 2 fst_InMembers. reflexivity.
      + now rewrite Hperm, <-fst_NoDupMembers.
      + intros ? Hin1. rewrite In_of_list_InMembers.
        eapply NoDupMembers_app_InMembers in Hnd; eauto.
      + intros ?. rewrite In_of_list_InMembers, <-InMembers_app, fst_InMembers, <-Hperm.
        apply Is_defined_in_vars_defined.
  Qed.

  Program Definition dce_node (n : node) : node :=
    let res := dce_eqs' n.(n_out) n.(n_vars) n.(n_eqs) in
    {| n_name := n.(n_name);
       n_in := n.(n_in);
       n_out := n.(n_out);
       n_vars := fst (proj1_sig res);
       n_eqs := snd (proj1_sig res)
    |}.
  Next Obligation. exact n.(n_ingt0). Qed.
  Next Obligation. exact n.(n_outgt0). Qed.
  Next Obligation.
    specialize (n_defd n) as Hdef.
    specialize (n_nodup n) as Hndup.
    eapply dce_vars_defined; eauto using NoDupMembers_app_r.
  Qed.
  Next Obligation.
    intro contra.
    eapply n_vout; eauto.
    rewrite <-Is_defined_in_vars_defined in *. unfold Is_defined_in in *.
    apply Exists_exists in contra as (?&Hin&Hdef).
    apply Exists_exists. repeat esplit; eauto.
    apply filter_In in Hin as (Hin&Hf1). apply filter_In in Hin as (Hin&_).
    apply filter_In; eauto.
  Qed.
  Next Obligation.
    specialize (n_nodup n) as Hnd.
    apply dce_NoDupMembers_filter; auto.
  Qed.
  Next Obligation.
    specialize (n_good n) as Hgood.
    repeat rewrite map_app, Forall_app in *.
    destruct Hgood as ((Hin&Hvar&Hout)&Hname).
    repeat (split; auto).
    apply Forall_map. rewrite Forall_map in Hvar.
    eapply Forall_incl; [|eapply incl_filter', incl_refl]. apply Hvar.
  Qed.

  Local Program Instance dce_node_transform_unit: TransformUnit node node :=
    { transform_unit := dce_node }.

  Local Program Instance dce_without_units: TransformProgramWithoutUnits global global :=
    { transform_program_without_units := fun g => Global g.(types) [] }.

  Definition dce_global : global -> global := transform_units.

  (** *** Some properties *)

  Lemma find_node_dce_forward : forall G f n,
      find_node f G = Some n ->
      find_node f (dce_global G) = Some (dce_node n).
  Proof.
    unfold dce_global, find_node.
    intros * Hfind.
    apply option_map_inv in Hfind as ((?&?)&Hfind&?); subst.
    apply find_unit_transform_units_forward in Hfind.
    rewrite Hfind; auto.
  Qed.

  Lemma find_node_dce_backward : forall G f n,
      find_node f (dce_global G) = Some n ->
      exists n0, find_node f G = Some n0 /\ n = dce_node n0.
  Proof.
    unfold dce_global, find_node.
    intros * Hfind.
    apply option_map_inv in Hfind as ((?&?)&Hfind&?); subst.
    apply find_unit_transform_units_backward in Hfind as (?&?&Hfind&?&?); subst.
    exists x. repeat split; auto.
    rewrite Hfind; auto.
  Qed.

  Lemma dce_global_iface_eq : forall G,
      global_iface_eq G (dce_global G).
  Proof.
    intros. split; intros; auto.
    destruct (find_node _ _) eqn:Hfind.
    - erewrite find_node_dce_forward; eauto.
      constructor; simpl.
      repeat (split; auto).
    - destruct (find_node f (dce_global _)) eqn:Hfind'; try constructor.
      exfalso.
      apply find_node_dce_backward in Hfind' as (?&?&_); congruence.
  Qed.

End DCE.

Module DCEFun
       (Ids   : IDS)
       (Op    : OPERATORS)
       (OpAux : OPERATORS_AUX   Ids Op)
       (Cks   : CLOCKS      Ids Op OpAux)
       (CESyn : CESYNTAX    Ids Op OpAux Cks)
       (CEF   : CEISFREE    Ids Op OpAux Cks CESyn)
       (Syn   : NLSYNTAX    Ids Op OpAux Cks CESyn)
       (Free  : ISFREE      Ids Op OpAux Cks CESyn Syn CEF)
       (Mem   : MEMORIES    Ids Op OpAux Cks CESyn Syn)
       (Def   : ISDEFINED   Ids Op OpAux Cks CESyn Syn Mem)
<: DCE Ids Op OpAux Cks CESyn CEF Syn Free Mem Def.
  Include DCE Ids Op OpAux Cks CESyn CEF Syn Free Mem Def.
End DCEFun.
