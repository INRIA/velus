From Coq Require Import List.
Import List.ListNotations.
Open Scope list_scope.

From Coq Require Import Recdef.
From Velus Require Import Common.
From Velus Require Import CommonProgram.
From Velus Require Import Operators.
From Velus Require Import Clocks.
From Velus Require Import Environment.
From Velus Require Import FunctionalEnvironment.
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

  Definition dep_graph := Env.t PS.t.

  Definition depends_on (gr : dep_graph) (x y : ident) :=
    exists s, Env.find x gr = Some s /\ PS.In y s.

  Definition add_deps (x : ident) (deps : PS.t) (gr : dep_graph) : dep_graph :=
    Env.add x (or_default_with deps (fun deps' => PS.union deps' deps) (Env.find x gr)) gr.
    (* match Env.find x gr with *)
    (* | Some deps' => Env.add x (PS.union deps' deps) gr *)
    (* | None => Env.add x deps gr *)
    (* end. *)

  Lemma add_deps_spec : forall i deps gr x y,
      depends_on (add_deps i deps gr) x y <-> (depends_on gr x y \/ x = i /\ PS.In y deps).
  Proof.
    intros. unfold add_deps, depends_on, or_default_with.
    destruct (ident_eq_dec x i); subst.
    - setoid_rewrite Env.gss.
      split; [intros (?&Find&In)|intros [(?&Find&In)|(?&In)]]; subst.
      + cases_eqn Eq; auto. inv Find.
        apply PS.union_spec in In as [|]; eauto.
      + rewrite Find; eauto using PSF.union_2.
      + cases; eauto using PSF.union_3.
    - setoid_rewrite Env.gso; auto.
      split; [intros|intros [|(?&?)]]; auto. contradiction.
  Qed.

  Lemma add_deps_In : forall i deps gr x,
      Env.In x (add_deps i deps gr) <-> (Env.In x gr \/ x = i).
  Proof.
    intros. unfold add_deps.
    rewrite Env.Props.P.F.add_in_iff.
    split; intros [|]; auto.
  Qed.

  Definition free_graph (eqs : list equation) : dep_graph :=
    fold_right (fun eq gr =>
                  let '(defs, defsl) := defined_eq (PS.empty, PS.empty) eq in
                  let defs := PS.union defs defsl in
                  let '(frees, freesl) := free_in_equation eq (PS.empty, PS.empty) in
                  let fdefs := PS.union (PS.union frees freesl) defs in
                  PS.fold (fun x => add_deps x fdefs) defs gr)
               (Env.empty _) eqs.

  Fact fold_In : forall defs (frees : PS.t) gr x,
      Env.In x (PS.fold (fun x => add_deps x frees) defs gr) <->
      PS.In x defs \/ Env.In x gr.
  Proof.
    intros *.
    apply PSP.fold_rec.
    - intros * Hemp. split; auto.
      intros [Hin|]; subst; auto.
      apply Hemp in Hin as [].
    - unfold PSP.Add.
      intros * Hin Hnin Hadd Hrec.
      rewrite add_deps_In, Hrec, Hadd.
      split; intros [[|]|]; auto.
  Qed.

  Lemma free_graph_In : forall x eqs,
      Env.In x (free_graph eqs) <-> Is_defined_in (Var x) eqs \/ Is_defined_in (Last x) eqs.
  Proof.
    unfold free_graph.
    split.
    - induction eqs; intros * Hin; simpl in *.
      + apply Env.Props.P.F.empty_in_iff in Hin; inv Hin.
      + cases_eqn Eq.
        apply fold_In in Hin as [Hin|]; [apply PS.union_spec in Hin as [Hin|Hin]|].
        * left; left. apply defined_eq_spec1. now rewrite Eq.
        * right; left. apply defined_eq_spec2. now rewrite Eq.
        * apply IHeqs in H as [|]; [left|right]; right; auto.
    - induction eqs; intros * Hin; simpl in *.
      + destruct Hin as [Hin|Hin]; inv Hin.
      + cases_eqn Eq.
        rewrite fold_In, PS.union_spec.
        destruct Hin as [Hin|Hin]; inv Hin; auto; left.
        * left. now rewrite defined_eq_spec1, Eq in H0.
        * right. now rewrite defined_eq_spec2, Eq in H0.
  Qed.

  Fact find_fold_spec : forall defs (frees : PS.t) gr x y,
      depends_on (PS.fold (fun x => add_deps x frees) defs gr) x y
      <-> depends_on gr x y \/ (PS.In x defs /\ PS.In y frees).
  Proof.
    intros *.
    apply PSP.fold_rec.
    - intros * Hemp. split; auto.
      intros [|(?&?)]; subst; auto.
      apply Hemp in H as [].
    - intros * Hin Hnin Hadd Hrec.
      unfold PSP.Add in *.
      rewrite add_deps_spec, Hrec, Hadd.
      split; [intros [[|(?&?)]|(?&?)]|intros [|([|]&?)]]; subst; auto.
  Qed.

  Lemma free_graph_spec : forall eqs,
      (forall x y, depends_on (free_graph eqs) x y <->
              Exists (fun eq => (Is_defined_in_eq (Var x) eq \/ Is_defined_in_eq (Last x) eq)
                             /\ (Is_free_in_eq (Var y) eq
                                \/ Is_free_in_eq (Last y) eq
                                \/ Is_defined_in_eq (Var y) eq
                                \/ Is_defined_in_eq (Last y) eq)) eqs).
  Proof.
    unfold free_graph; split.
    - induction eqs; intros * * Dep; simpl in *; subst.
      + destruct Dep as (?&Find&_). rewrite Env.gempty in Find. congruence.
      + cases_eqn Eq.
        apply find_fold_spec in Dep as [Dep|(In1&In2)]; auto.
        left. rewrite PSF.union_iff in In1. rewrite 3 PSF.union_iff in In2.
        rewrite 2 defined_eq_spec1, 2 defined_eq_spec2, <-free_in_equation_spec1', <-free_in_equation_spec2', Eq, Eq0.
        split; auto. repeat take (_ \/ _) and destruct it; auto.
    - induction eqs; intros * * Hex; simpl in *. inv Hex.
      cases_eqn Eq.
      inv Hex.
      + clear IHeqs.
        rewrite 2 defined_eq_spec1, 2 defined_eq_spec2, <-free_in_equation_spec1', <-free_in_equation_spec2', Eq, Eq0 in H0.
        destruct H0 as (Def&Free).
        rewrite find_fold_spec. right.
        rewrite 4 PSF.union_iff. repeat take (_ \/ _) and destruct it; auto.
      + apply IHeqs in H0; eauto.
        rewrite find_fold_spec; auto.
  Qed.

  (** *** Calculate the set of unused variables *)

  Section compute_unused.

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
        (forall y, PS.In y (fst whgs1) \/ PS.In y (snd whgs1) -> depends_on gr y x -> PS.In y wh2).
    Proof.
      intros * Hgr Hnd. revert wh2.
      functional induction (compute_unused whgs1); destruct whgs as (wh1&gs1); simpl in *.
      - intros * ? Hin; subst.
        split; auto.
        intros ? [|]; auto. exfalso.
        apply PS.choose_spec2 in e. apply e in H; auto.
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
        intros ? Hin1 (?&Hfind'&Hin').
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
        eapply Hrec2; eauto. do 2 esplit; eauto.
    Qed.

  End compute_unused.

  Definition dce_eqs (outs : PS.t) (vars : list (ident * (type * clock * bool))) (eqs : list equation) :=
    let gr := free_graph eqs in
    let unused := compute_unused gr (PSP.of_list (map fst vars), outs) in
    (List.filter (fun '(x, _) => negb (PS.mem x unused)) vars,
     List.filter (fun eq => let '(defs, defsl) := defined_eq (PS.empty, PS.empty) eq in
                         PS.for_all (fun x => negb (PS.mem x unused)) (PS.union defs defsl)) eqs).

  Lemma dce_eqs_vars_defined : forall outs vars eqs vars' eqs',
      (forall x, InMembers x vars -> ~PS.In x outs) ->
      (forall x, Is_defined_in (Var x) eqs <-> InMembers x vars \/ PS.In x outs) ->
      dce_eqs outs vars eqs = (vars', eqs') ->
      (forall x, Is_defined_in (Var x) eqs' <-> InMembers x vars' \/ PS.In x outs).
  Proof.
    unfold dce_eqs.
    intros * Hnd Hdef Hdce. inv Hdce.
    unfold Is_defined_in in *.
    intros x. rewrite filter_InMembers, Exists_exists. setoid_rewrite filter_In.
    setoid_rewrite Exists_exists in Hdef.
    split.
    - intros (?&(Hineqs&Hf)&Hisdef). cases_eqn Eq.
      edestruct Hdef as ([Hin|]&_); eauto.
      apply InMembers_In in Hin as (?&Hin).
      left. repeat esplit; eauto.
      apply PS.for_all_spec in Hf. 2:{ intros ?? Heq; inv Heq; auto. }
      rewrite defined_eq_spec1, Eq in Hisdef.
      apply Hf, PS.union_spec; auto.
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
          apply free_graph_In. left. apply Exists_exists, Hdef.
          destruct Hin1; auto. left. apply In_of_list_InMembers; auto.
        - intros ??. apply Hnd, In_of_list_InMembers; auto.
      }
      edestruct Hdef as (_&(?&?&Def)).
      + destruct Hin as [((?&?)&?&?)|]; eauto using In_InMembers.
      + repeat esplit; eauto. cases_eqn Eq.
        eapply PS.for_all_spec. 1:{ intros ?? Heq; inv Heq; auto. }
        intros ? Hisdef. rewrite defined_eq_spec1, Eq in Def.
        apply Bool.negb_true_iff, PSP.FM.not_mem_iff.
        intros Hin'.
        assert (Hcomp:=Hin'). eapply compute_unused_stable in Hcomp. 4:reflexivity. 1-3:simpl in *.
        * destruct Hcomp as (Hin1&Hin2).
          assert (depends_on (free_graph eqs) x x1) as Dep.
          { eapply free_graph_spec; eauto.
            solve_Exists. rewrite 2 defined_eq_spec1, 2 defined_eq_spec2, Eq.
            apply PS.union_spec in Hisdef as [|]; auto.
          }
          eapply Hnin in Hin2; eauto.
          rewrite In_of_list_InMembers. eapply Hdef. do 2 esplit; eauto.
          rewrite defined_eq_spec1, Eq; auto.
        * intros ? Hin1.
          apply free_graph_In. left. apply Exists_exists, Hdef.
          destruct Hin1; auto. left. apply In_of_list_InMembers; auto.
        * intros ??. apply Hnd, In_of_list_InMembers; auto.
  Qed.

  Lemma dce_eqs_lasts_defined : forall outs vars eqs vars' eqs',
      (forall x, InMembers x vars -> ~PS.In x outs) ->
      (forall x, Is_defined_in (Var x) eqs <-> InMembers x vars \/ PS.In x outs) ->
      (forall x, Is_defined_in (Last x) eqs <-> exists ty ck, In (x, (ty, ck, true)) vars) ->
      dce_eqs outs vars eqs = (vars', eqs') ->
      (forall x, Is_defined_in (Last x) eqs' <-> exists ty ck, In (x, (ty, ck, true)) vars').
  Proof.
    unfold dce_eqs.
    intros * Hnd Vars Lasts Hdce. inv Hdce.
    unfold Is_defined_in in *.
    intros x. rewrite Exists_exists. setoid_rewrite filter_In.
    setoid_rewrite Exists_exists in Lasts.
    split.
    - intros (?&(Hineqs&Hf)&Hisdef). cases_eqn Eq.
      edestruct Lasts as ((?&?&In)&_); eauto.
      repeat esplit; eauto.
      apply PS.for_all_spec in Hf. 2:{ intros ?? Heq; inv Heq; auto. }
      rewrite defined_eq_spec2, Eq in Hisdef.
      apply Hf, PS.union_spec; auto.
    - intros Hin.
      assert (~PS.In x (compute_unused (free_graph eqs) (PSP.of_list (map fst vars), outs))) as Hnin.
      { intro Hin2.
        assert (Hcomp:=Hin2). eapply compute_unused_stable in Hcomp. 4:reflexivity. 1-3:simpl in *.
        - destruct Hcomp as (Hin1&_).
          apply In_of_list_InMembers in Hin1.
          destruct Hin as (?&?&_&Hneg).
          apply Bool.negb_true_iff, PSP.FM.not_mem_iff in Hneg.
          contradiction.
        - intros ? Hin1.
          apply free_graph_In. left. apply Vars.
          destruct Hin1; auto. left. apply In_of_list_InMembers; auto.
        - intros ??. apply Hnd, In_of_list_InMembers; auto.
      }
      edestruct Lasts as (_&(?&?&Def)).
      + destruct Hin as (?&?&?&?); eauto using In_InMembers.
      + repeat esplit; eauto. cases_eqn Eq.
        eapply PS.for_all_spec. 1:{ intros ?? Heq; inv Heq; auto. }
        intros ? Hisdef. rewrite defined_eq_spec2, Eq in Def.
        apply Bool.negb_true_iff, PSP.FM.not_mem_iff.
        intros Hin'.
        assert (Hcomp:=Hin'). eapply compute_unused_stable in Hcomp. 4:reflexivity. 1-3:simpl in *.
        * destruct Hcomp as (Hin1&Hin2).
          assert (depends_on (free_graph eqs) x x1) as Dep.
          { eapply free_graph_spec; eauto.
            solve_Exists. rewrite 2 defined_eq_spec1, 2 defined_eq_spec2, Eq.
            apply PS.union_spec in Hisdef as [|]; auto.
          }
          eapply Hnin in Hin2; eauto.
          rewrite In_of_list_InMembers. left. edestruct Lasts as ((?&?&L)&_); eauto. 2:solve_In.
          do 2 esplit; eauto. rewrite defined_eq_spec2, Eq; auto.
        * intros ? Hin1.
          apply free_graph_In. left. apply Vars.
          destruct Hin1; auto. left. apply In_of_list_InMembers; auto.
        * intros ??. apply Hnd, In_of_list_InMembers; auto.
  Qed.

  Lemma dce_eqs_stable : forall (ins vars outs : list (ident * (type * clock * bool))) eqs vars' eqs',
      (forall x, InMembers x vars -> ~InMembers x outs) ->
      (forall x, InMembers x (vars ++ outs) <-> Is_defined_in (Var x) eqs) ->
      (forall x, Is_defined_in (Last x) eqs -> InMembers x vars) ->
      Forall (fun eq => exists x, Is_defined_in_eq x eq) eqs ->
      (forall x, Exists (fun eq => (Is_defined_in_eq x eq \/ Is_free_in_eq x eq)) eqs ->
            InMembers (var_last_ident x) (ins ++ vars ++ outs)) ->
      dce_eqs (PSP.of_list (map fst outs)) vars eqs = (vars', eqs') ->
      (forall x, Exists (fun eq => (Is_defined_in_eq x eq \/ Is_free_in_eq x eq)) eqs' ->
            InMembers (var_last_ident x) (ins ++ vars' ++ outs)).
  Proof.
    unfold dce_eqs.
    intros * Hnd2 Vars Lasts Hvd Hex1 Hdce * Hex. inv Hdce.
    repeat rewrite InMembers_app.
    apply Exists_exists in Hex as (?&Hin&Hex). simpl_In.
    cases_eqn Eq.
    apply PS.for_all_spec in Hf. 2:{ intros ?? Heq; inv Heq; auto. }
    specialize (Hex1 x). rewrite Exists_exists in Hex1.
    rewrite 2 InMembers_app, 3 fst_InMembers in Hex1. destruct Hex1 as [|[Hin'|]]; eauto.
    right; left. solve_In.
    destruct Hex as [Hex|Hex].
    - apply Hf, PS.union_spec.
      destruct x; subst; rewrite ?defined_eq_spec1, ?defined_eq_spec2, Eq in Hex; auto.
    - apply Bool.negb_true_iff, PSF.not_mem_iff.
      intros Hcomp.
      eapply compute_unused_stable in Hcomp as (Hcomp1&Hcomp2). 4:reflexivity. 1-3:simpl in *.
      + eapply Forall_forall in Hvd as (y&Hvd); eauto.
        assert (depends_on (free_graph eqs) (var_last_ident y) (var_last_ident x)) as Dep.
        { eapply free_graph_spec; eauto.
          solve_Exists. destruct x, y; subst; auto. }
        assert (PS.In (var_last_ident y) (PS.union t t0)) as In.
        { rewrite PS.union_spec.
          destruct y; subst; rewrite ?defined_eq_spec1, ?defined_eq_spec2, Eq in Hvd; auto. }
        eapply Hcomp2 in Dep; eauto.
        2:{ rewrite 2 In_of_list_InMembers; eauto using In_InMembers.
            destruct y; subst.
            - rewrite <-InMembers_app. apply Vars, Exists_exists; eauto.
            - left. apply Lasts, Exists_exists; eauto. }
        rewrite PSF.mem_iff in Dep.
        specialize (Hf (var_last_ident y) In). simpl in Hf. rewrite Dep in Hf. simpl in *. congruence.
      + intros ? Hin1.
        apply free_graph_In. left. apply Vars.
        rewrite 2 In_of_list_InMembers in Hin1.
        rewrite InMembers_app; auto.
      + intros ?. rewrite 2 In_of_list_InMembers; auto.
  Qed.

  (** ** Transformation of the node and global *)

  Import Permutation.

  Definition dce_eqs' (outs: list (ident * (type * clock))) (vars: list (ident * (type * clock * bool))) eqs :
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

  Fact lasts_defined_filter_In : forall p eqs x,
      In x (lasts_defined (filter p eqs)) ->
      In x (lasts_defined eqs).
  Proof.
    induction eqs; intros * Hin; simpl in *; auto.
    destruct (p a); simpl in *; eauto with datatypes.
    apply in_app_iff in Hin as [|]; eauto with datatypes.
  Qed.

  Corollary lasts_defined_filter_NoDup : forall p eqs,
      NoDup (lasts_defined eqs) ->
      NoDup (lasts_defined (filter p eqs)).
  Proof.
    induction eqs; intros * Hnd; simpl in *; auto.
    destruct (p a); simpl; eauto using NoDup_app_r.
    eapply NoDup_app'; eauto using NoDup_app_l, NoDup_app_r.
    eapply Forall_forall; intros ? Hin1 Hin2.
    eapply NoDup_app_In in Hnd; eauto.
    eapply Hnd, lasts_defined_filter_In; eauto.
  Qed.

  Fact dce_NoDupMembers_filter {A B} : forall (ins outs : list (ident * A)) (vars : list (ident * B)) p,
      NoDup (map fst ins ++ map fst vars ++ map fst outs) ->
      NoDup (map fst ins ++ map fst (filter p vars) ++ map fst outs).
  Proof.
    intros * Hnd.
    repeat apply NoDup_app'; eauto using NoDup_app_l, NoDup_app_r.
    - apply fst_NoDupMembers, NoDupMembers_filter, fst_NoDupMembers; eauto using NoDup_app_l, NoDup_app_r.
    - simpl_Forall. simpl_In.
      eapply NoDup_app_r, NoDup_app_In in Hnd; eauto. solve_In.
    - simpl_Forall. simpl_In.
      eapply NoDup_app_In in Hnd; [|solve_In].
      contradict Hnd. rewrite in_app_iff in *. destruct Hnd; [left|right]; solve_In.
  Qed.

  Fact dce_vars_defined {A} : forall eqs vars (outs: list (ident * A)) vars' eqs',
      NoDup (map fst vars ++ map fst outs) ->
      Permutation (vars_defined eqs) (map fst vars ++ map fst outs) ->
      dce_eqs (PSP.of_list (map fst outs)) vars eqs = (vars', eqs') ->
      Permutation (vars_defined eqs') (map fst vars' ++ map fst outs).
  Proof.
    intros * Hnd Hperm Hdce. inv Hdce.
    apply NoDup_Permutation.
    - apply vars_defined_filter_NoDup. now rewrite Hperm.
    - apply NoDup_app'; eauto using NoDup_app_r.
      + apply fst_NoDupMembers, NoDupMembers_filter, fst_NoDupMembers; eauto using NoDup_app_l.
      + simpl_Forall. simpl_In.
        eapply NoDup_app_In; eauto. solve_In.
    - intros ?. rewrite <-Is_defined_in_vars_defined, dce_eqs_vars_defined.
      4:unfold dce_eqs; reflexivity.
      + rewrite in_app_iff, In_of_list_InMembers, 2 fst_InMembers. reflexivity.
      + intros ? Hin1. rewrite In_of_list_InMembers, fst_InMembers.
        eapply NoDup_app_In; eauto. solve_In.
      + intros ?. rewrite In_of_list_InMembers, 2 fst_InMembers, <-in_app_iff, <-Hperm.
        apply Is_defined_in_vars_defined.
  Qed.

  Fact dce_lasts_defined {A} : forall eqs vars (outs: list (ident * A)) vars' eqs',
      NoDup (map fst vars ++ map fst outs) ->
      Permutation (vars_defined eqs) (map fst vars ++ map fst outs) ->
      Permutation (lasts_defined eqs) (map fst (filter (fun '(_, (_, _, islast)) => islast) vars)) ->
      dce_eqs (PSP.of_list (map fst outs)) vars eqs = (vars', eqs') ->
      Permutation (lasts_defined eqs') (map fst (filter (fun '(_, (_, _, islast)) => islast) vars')).
  Proof.
    intros * Hnd Vars Lasts Hdce. inv Hdce.
    apply NoDup_Permutation.
    - apply lasts_defined_filter_NoDup. rewrite Lasts.
      apply fst_NoDupMembers, NoDupMembers_filter, fst_NoDupMembers; eauto using NoDup_app_l.
    - apply fst_NoDupMembers, NoDupMembers_filter, NoDupMembers_filter, fst_NoDupMembers; eauto using NoDup_app_l.
    - intros ?. rewrite <-Is_defined_in_lasts_defined, dce_eqs_lasts_defined.
      5:unfold dce_eqs; reflexivity.
      + split; [intros (?&?&?)|intros; simpl_In; do 2 esplit]; solve_In; eauto.
      + intros ? Hin1. rewrite In_of_list_InMembers, fst_InMembers.
        eapply NoDup_app_In; eauto. solve_In.
      + intros ?. rewrite In_of_list_InMembers, 2 fst_InMembers, <-in_app_iff, <-Vars.
        apply Is_defined_in_vars_defined.
      + intros ?. rewrite Is_defined_in_lasts_defined, Lasts.
        split; [intros; simpl_In; do 2 esplit|intros (?&?&?)]; eauto; solve_In.
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
    eapply dce_vars_defined; eauto using NoDup_app_r.
  Qed.
  Next Obligation.
    specialize (n_defd n) as Hdef.
    specialize (n_lastd1 n) as Hlasts.
    specialize (n_nodup n) as Hndup.
    eapply dce_lasts_defined; eauto using NoDup_app_r.
  Qed.
  Next Obligation.
    simpl_In.
    apply n_lastd2 in Hin.
    rewrite <-Is_defined_in_vars_defined in *. unfold Is_defined_in in *.
    solve_Exists. solve_In.
    destruct x0; simpl in *; try congruence. inv Hin.
    apply PS.for_all_spec; [intros ?? Eq; now inv Eq|].
    apply PS_For_all_union; [apply PS_For_all_add|]; auto using PS_For_all_empty.
  Qed.
  Next Obligation.
    intro contra.
    eapply n_vout; eauto.
    rewrite <-Is_defined_in_vars_defined in *. unfold Is_defined_in in *.
    solve_Exists. solve_In.
  Qed.
  Next Obligation.
    specialize (n_nodup n) as Hnd.
    apply dce_NoDupMembers_filter; auto.
  Qed.
  Next Obligation.
    specialize (n_good n) as Hgood.
    repeat rewrite Forall_app in *.
    destruct Hgood as ((Hin&Hvar&Hout)&Hname).
    repeat (split; auto).
    simpl_Forall. simpl_In. simpl_Forall. auto.
  Qed.

  Local Program Instance dce_node_transform_unit: TransformUnit node node :=
    { transform_unit := dce_node }.

  Local Program Instance dce_without_units: TransformProgramWithoutUnits global global :=
    { transform_program_without_units := fun g => Global g.(types) g.(externs) [] }.

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
    intros. repeat split; intros; auto.
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
