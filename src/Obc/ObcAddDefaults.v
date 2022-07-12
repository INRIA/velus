From Coq Require Import FSets.FMapPositive.
From Coq Require Import PArith.
From Velus Require Import Common.
From Velus Require Import CommonTyping.
From Velus Require Import Environment.
From Velus Require Import Operators.
From Velus Require Import Obc.ObcSyntax.
From Velus Require Import Obc.ObcSemantics.
From Velus Require Import Obc.ObcInvariants.
From Velus Require Import Obc.ObcTyping.
From Velus Require Import Obc.Equiv.

From Velus Require Import VelusMemory.

From Coq Require Import List.
Import List.ListNotations.
Open Scope list_scope.

Import Env.Notations.

From Coq Require Import Morphisms.

Module Type OBCADDDEFAULTS
       (Import Ids   : IDS)
       (Import Op    : OPERATORS)
       (Import OpAux : OPERATORS_AUX Ids Op)
       (Import SynObc: OBCSYNTAX     Ids Op OpAux)
       (Import ComTyp: COMMONTYPING  Ids Op OpAux)
       (Import SemObc: OBCSEMANTICS  Ids Op OpAux SynObc)
       (Import InvObc: OBCINVARIANTS Ids Op OpAux SynObc        SemObc)
       (Import TypObc: OBCTYPING     Ids Op OpAux SynObc ComTyp SemObc)
       (Import Equ   : EQUIV         Ids Op OpAux SynObc ComTyp SemObc TypObc).

  Definition PS_inter_list (l: list PS.t) :=
    reduce PS.inter l PS.empty.

  (* XXX XXX XXX TODO: Tidy this up and also in the lemmas *)
  Notation "x '∈' y" := (PS.In x y) (at level 10).
  Notation "a '⊆' b" := (PS.Subset a b) (at level 10).
  Notation "x '∪' y" := (PS.union x y) (at level 11, right associativity).
  Notation "x '∩' y" := (PS.inter x y) (at level 11, right associativity).
  Notation "x '\' y" := (PS.diff x y) (at level 11).
  Notation "'⋂' l" := (PS_inter_list l) (at level 9).
  Notation "'∅'" := (PS.empty).

  Ltac PS_split :=
    repeat match goal with
           | H: context [ PS.union _ _ ] |- _ => setoid_rewrite PS.union_spec in H
           | H: context [ ~(PS.inter _ _) ] |- _ => setoid_rewrite PS_not_inter in H
           | H: context [ PS.inter _ _ ] |- _ => setoid_rewrite PS.inter_spec in H
           | H: context [ PS.diff _ _ ] |- _ => setoid_rewrite PS.diff_spec in H
           | H: context [ ~(_ \/ _) ] |- _ => setoid_rewrite not_or' in H
           | H: context [ ~~PS.In _ _ ] |- _ => setoid_rewrite not_not_in in H
           | H: context [ PS.In _ PS.empty ] |- _ => setoid_rewrite PSF.empty_iff in H
           | H: context [ PS.In _ PS.Leaf ] |- _ => setoid_rewrite PSF.empty_iff in H
           | H:_ /\ _ |- _ => destruct H
           | |- context [ PS.union _ _ ] => setoid_rewrite PS.union_spec
           | |- context [ ~(PS.inter _ _) ] => setoid_rewrite PS_not_inter
           | |- context [ PS.inter _ _ ] => setoid_rewrite PS.inter_spec
           | |- context [ PS.diff _ _ ] => setoid_rewrite PS.diff_spec
           | |- context [ ~(_ \/ _) ] => setoid_rewrite not_or'
           | |- context [ ~~PS.In _ _ ] => setoid_rewrite not_not_in
           | |- context [ PS.In _ PS.empty ] => setoid_rewrite PSF.empty_iff
           | |- context [ PS.In _ PS.Leaf ] => setoid_rewrite PSF.empty_iff
           end.

  Ltac PS_negate :=
    repeat match goal with
           | H:~(_ /\ _) |- _ => apply Decidable.not_and in H; [|now intuition]
           | H:~~_ |- _ => apply Decidable.not_not in H; [|now intuition]
           | H: context [ ~~PS.In _ _ ] |- _ => rewrite not_not_in in H
           end.

  Lemma In_fold_left_inter:
    forall l s x,
      x ∈ (fold_left PS.inter l s) <-> Forall (PS.In x) l /\ x ∈ s.
  Proof.
    induction l; simpl; split; auto.
    - intuition.
    - intros * Hin; apply IHl in Hin as [].
      PS_split; auto.
    - intros * [Hl]; inv Hl.
      apply IHl; PS_split; auto.
  Qed.

  (** ** AddDefault functions *)

  Section AddDefaults.

    Variable type_of_var : ident -> option type.

    Definition add_write x s :=
      match type_of_var x with
      | None => s
      | Some (Tprimitive ty) => Comp (Assign x (Const (init_ctype ty))) s
      | Some (Tenum tx tn) => Comp (Assign x (Enum 0 (Tenum tx tn))) s
      end.

    Definition add_writes W s := PS.fold add_write W s.

    Definition add_valid (e : exp) (esreq : list exp * PS.t) :=
      match e with
      | Var x ty => (Valid x ty :: fst esreq, PS.add x (snd esreq))
      | _ => (e :: fst esreq, snd esreq)
      end.

    Lemma No_Naked_Vars_add_writes:
      forall W s,
        No_Naked_Vars s <-> No_Naked_Vars (add_writes W s).
    Proof.
      unfold add_writes.
      setoid_rewrite PSE.MP.fold_spec_right.
      intros.
      remember (rev (PS.elements W)) as ws.
      setoid_rewrite <-Heqws; clear Heqws.
      induction ws as [|w ws IH']; simpl. reflexivity.
      unfold add_write.
      rewrite IH'.
      destruct (type_of_var w) as [[]|]; split; intro HH; auto with obcinv;
        inversion_clear HH; auto.
    Qed.

    Lemma Can_write_in_add_writes_mono:
      forall s W x,
        Can_write_in_var x s ->
        Can_write_in_var x (add_writes W s).
    Proof.
      intros * Hcan.
      setoid_rewrite PSE.MP.fold_spec_right.
      remember (rev (PS.elements W)) as ws.
      setoid_rewrite <-Heqws. clear Heqws W.
      induction ws as [|w ws IH]; auto with obcinv.
      simpl. unfold add_write at 1.
      cases; auto with obcinv.
    Qed.

    Lemma Can_write_in_add_writes:
      forall s W x,
        Can_write_in_var x (add_writes W s) ->
        x ∈ W \/ Can_write_in_var x s.
    Proof.
      setoid_rewrite PSE.MP.fold_spec_right; intros ???.
      remember (rev (PS.elements W)) as ws.
      assert (forall x, x ∈ W <-> In x ws) as HinW.
      { intro y; subst ws. rewrite <-in_rev, PSF.elements_iff.
        split; intro HH; auto using SetoidList.In_InA. apply SetoidList.InA_alt in HH.
        destruct HH as (? & ? & ?); subst; eauto. }
      setoid_rewrite <-Heqws; rewrite HinW; clear Heqws HinW W.
      induction ws as [|w ws IH]; auto.
      simpl. unfold add_write at 1.
      destruct (type_of_var w); [intro Hcw|now intuition].
      destruct t; inversion_clear Hcw as [| | | |? ? ? Hcw'|? ? ? Hcw'];
        try (now inversion_clear Hcw'; auto); intuition.
    Qed.

    Lemma stmt_eval_add_writes_split:
      forall p s W me ve me'' ve'',
        stmt_eval p me ve (add_writes W s) (me'', ve'') <->
        (exists me' ve',
            stmt_eval p me ve (add_writes W Skip) (me', ve')
            /\ stmt_eval p me' ve' s (me'', ve'')).
    Proof.
      unfold add_writes.
      setoid_rewrite PSE.MP.fold_spec_right.
      intros until ve''.
      remember (rev (PS.elements W)) as ws.
      setoid_rewrite <-Heqws; clear Heqws W.
      revert s me ve me'' ve''.
      induction ws as [|w ws IH]; simpl; split; eauto using stmt_eval.
      - intros (me' & ve' & Heval1 & Heval2). now inv Heval1.
      - unfold add_write at 1 3. intro Heval.
        destruct (type_of_var w) as [[]|].
        + inversion_clear Heval as [| | | |? ? ? ? ? ? ? ? ? Heval1 Heval2| |].
          apply IH in Heval2 as (me' & ve' & Heval1' & Heval2'). eauto using stmt_eval.
        + inversion_clear Heval as [| | | |? ? ? ? ? ? ? ? ? Heval1 Heval2| |].
          apply IH in Heval2 as (me' & ve' & Heval1' & Heval2'). eauto using stmt_eval.
        + apply IH in Heval as (me' & ve' & Heval1' & Heval2'). eauto.
      - unfold add_write at 1 3. intros (me' & ve' & Heval1 & Heval3).
        destruct (type_of_var w) as [[]|].
        + inversion_clear Heval1 as [| | | |? ? ? ? ? ? ? ? ? Heval1' Heval2| |].
          econstructor; [now eapply Heval1'|]. apply IH; eauto.
        + inversion_clear Heval1 as [| | | |? ? ? ? ? ? ? ? ? Heval1' Heval2| |].
          econstructor; [now eapply Heval1'|]. apply IH; eauto.
        + apply IH; eauto.
    Qed.

    Lemma stmt_eval_add_writes_Skip_other:
      forall p W me ve me' ve',
        stmt_eval p me ve (add_writes W Skip) (me', ve') ->
        forall x, ~ x ∈ W ->
             Env.find x ve' = Env.find x ve.
    Proof.
      setoid_rewrite PSE.MP.fold_spec_right.
      intros until ve'.
      remember (rev (PS.elements W)) as ws.
      assert (forall x, x ∈ W <-> In x ws) as HinW.
      { intro x; subst ws. rewrite <-in_rev, PSF.elements_iff.
        split; intro HH; auto using SetoidList.In_InA. apply SetoidList.InA_alt in HH.
        destruct HH as (? & ? & ?); subst; eauto. }
      setoid_rewrite HinW. setoid_rewrite <-Heqws.
      clear Heqws HinW W.
      revert me ve me' ve'.
      induction ws as [|w ws IH]. now inversion 1.
      simpl. intros * Heval x Hin.
      apply Decidable.not_or in Hin.
      destruct Hin as (Hnwx & Hnin).
      unfold add_write in Heval. destruct (type_of_var w) as [[]|].
      - inversion_clear Heval as [| | | |? ? ? ? ? ? ? ? ? Heval1 Heval2| |].
        apply IH with (x:=x) in Heval2; auto. rewrite Heval2.
        inv Heval1. rewrite Env.gso; auto.
      - inversion_clear Heval as [| | | |? ? ? ? ? ? ? ? ? Heval1 Heval2| |].
        apply IH with (x:=x) in Heval2; auto. rewrite Heval2.
        inv Heval1. rewrite Env.gso; auto.
      - apply IH with (x:=x) in Heval; auto.
    Qed.

    Lemma stmt_eval_add_writes:
      forall p s W me ve me' ve',
        PS.For_all (fun x => type_of_var x <> None) W ->
        stmt_eval p me ve (add_writes W s) (me', ve') ->
        PS.For_all (fun x => Env.In x ve') W.
    Proof.
      intros p.
      unfold add_writes.
      setoid_rewrite PSE.MP.fold_spec_right.
      intros until ve'.
      remember (rev (PS.elements W)) as ws.
      assert (forall x, x ∈ W <-> In x ws) as HinW.
      { intro x; subst ws. rewrite <-in_rev, PSF.elements_iff.
        split; intro HH; auto using SetoidList.In_InA. apply SetoidList.InA_alt in HH.
        destruct HH as (? & ? & ?); subst; eauto. }
      setoid_rewrite PS_For_all_Forall.
      setoid_rewrite (Permutation.Permutation_rev (PS.elements W)) at 1 3.
      setoid_rewrite <-Heqws.
      clear Heqws HinW W.
      revert s me ve me' ve'.
      induction ws as [|w ws IH]; eauto.
      simpl. intros * Hfa Heval.
      inversion_clear Hfa as [|? ? Hnn Hws].
      unfold add_write in Heval.
      apply not_None_is_Some in Hnn; destruct Hnn as (wv & Hnn).
      rewrite Hnn in Heval.
      destruct wv; inversion_clear Heval as [| | | |? ? ? ? ? ? ? Ha Hb Heval1 Heval2| |].
      - pose proof (stmt_eval_mono _ _ _ _ _ _ Heval2) as Henv1'.
        apply IH in Heval2; auto.
        constructor; auto.
        apply Henv1'. inv Heval1.
        apply Env.Props.P.F.add_in_iff; auto.
      - pose proof (stmt_eval_mono _ _ _ _ _ _ Heval2) as Henv1'.
        apply IH in Heval2; auto.
        constructor; auto.
        apply Henv1'. inv Heval1.
        apply Env.Props.P.F.add_in_iff; auto.
    Qed.

    (* [(s', required', sometimes, always) = add_defaults_stmt (s, required)]

       Transforms [s] into [s'] by
       - Adding [Valid]s around "naked variables" in function calls.
       - Adding initializing writes to satisfy [required].

       [required] is a set of variables that must be written or otherwise
       initialized by [s] or a statement executed before [s].

       The output sets are:
       - [required']: updated set of variables to write or initialize
       - [sometimes]: variables that may be written in s
       - [always]: variables always written in s

       with [PS.is_empty (PS.inter sometimes always)] and knowing that a
       variable is never written if it is neither in [sometimes] nor [always].

       This function is designed to optimize code produced by compiling and
       then "fusion-ing" NLustre code, but proofs of the invariant properties
       do not rely on this fact (since that would require precisely expressing
       and tracking the assumptions).
       Notably, for Ifte, it should always be the case that
       [sometimes1' = sometimes1] and [sometimes2' = sometimes2].

       Switches are treated in 2 ways:
       - if their "arity" is 2, then we use the analysis for former if/the/else
         (see JFLA 2019 paper)
       - otherwise, the analysis is simpler: additional assignments are pushed
         at the beginning of the switch, without entering into the branches, to
         ensure a decent trade-off between code size and unneeded assignments
     *)

    Section AddDefaultsSwitch.

      Variables (add_defaults_stmt: stmt -> stmt * PS.t * PS.t * PS.t)
                (required: PS.t).

      Definition add_defaults_ite (e: exp) (s1 s2: stmt)
        : stmt * PS.t * PS.t * PS.t :=
        let '(t1, required1, sometimes1, always1) := add_defaults_stmt s1 in
        let '(t2, required2, sometimes2, always2) := add_defaults_stmt s2 in
        let always1_req := always1 ∩ required in
        let always2_req := always2 ∩ required in
        let w1 := always2_req \ always1_req in
        let w2 := always1_req \ always2_req in
        let w := ((sometimes1 ∩ required) \ w1) ∪ ((sometimes2 ∩ required) \ w2) in
        let always1' := always1 ∪ w1 in
        let always2' := always2 ∪ w2 in
        let sometimes1' := sometimes1 \ w1 in
        let sometimes2' := sometimes2 \ w2 in
        (add_writes w (Switch e [Some (add_writes w1 t1); None] (add_writes w2 t2)),
         (((((required \ always1_req) \ always2_req)) ∪ required1) ∪ required2) \ w,
         (sometimes1' ∪ (sometimes2' ∪ ((always1' \ always2') ∪ (always2' \ always1')))) \ w,
         (always1' ∩ always2') ∪ w).

      Definition add_defaults_branches (ss: list (option stmt)) (d: stmt)
        : list (option stmt) * stmt * PS.t * PS.t * PS.t :=
        let '(d, req_d, st_d, al_d) := add_defaults_stmt d in
        let '(ss, r, s, a) :=
            reduce_with (fun acc =>
                           let '(oss, r, s, a) := acc in
                           or_default_with
                             (None :: oss,
                              r ∪ req_d,
                              s ∪ st_d ∪ al_d,
                              a ∩ al_d)
                             (fun t =>
                                let '(t, req_s, st_s, al_s) := add_defaults_stmt t in
                                (Some t :: oss,
                                 r ∪ req_s,
                                 s ∪ st_s ∪ al_s,
                                 a ∩ al_s)))
                        ss ([], ∅, ∅, ∅)
                        (or_default_with
                           ([None], req_d, st_d ∪ al_d, al_d)
                           (fun t =>
                              let '(t, req_s, st_s, al_s) := add_defaults_stmt t in
                              ([Some t], req_s, st_s ∪ al_s, al_s)))
        in
        (rev ss, d, r, s, a).

      Definition add_defaults_switch (e: exp) (ss: list (option stmt)) (d: stmt)
        : stmt * PS.t * PS.t * PS.t :=
        let '(ss, d, r, s, a) := add_defaults_branches ss d in
        let w := (s \ a) ∩ required in
        (add_writes w (Switch e ss d),
         ((required \ a) ∪ r) \ w, (* NB: a and r are disjoint. *)
         (s \ a) \ required,
         (s ∩ required) ∪ a).

      Section Properties.

        Variables (d: stmt) (ss: list (option stmt)).

        Lemma add_defaults_branches_length:
          forall d' ss' r s a,
            add_defaults_branches ss d = (ss', d', r, s, a) ->
            length ss = length ss'.
        Proof.
          unfold add_defaults_branches.
          intros * Hadd.
          destruct (add_defaults_stmt d) as [[[d'' r_d] s_d] a_d].
          destruct ss as [|os ss'']; simpl.
          - inv Hadd; auto.
          - setoid_rewrite <-fold_left_rev_right in Hadd.
            rewrite <-rev_length.
            revert dependent r; revert s a ss'.
            induction (rev ss'') as [|os']; simpl in *; intros.
            + destruct os as [s'|]; simpl in *.
              * destruct (add_defaults_stmt s') as [[[t r_t] s_t] a_t].
                inv Hadd; auto.
              * inv Hadd; auto.
            + assert (d' = d'') by cases; subst d''.
              destruct (fold_right _ _ _) as [[[ss_l r_l] s_l] aa_l].
              erewrite IHl; eauto.
              destruct os' as [s'|]; simpl in *.
              * destruct (add_defaults_stmt s') as [[[t r_t] s_t] a_t].
                inv Hadd.
                rewrite app_length; simpl; lia.
              * inv Hadd.
                rewrite app_length; simpl; lia.
        Qed.

        Lemma add_defaults_switch_empty_stimes_always:
          forall e t req stimes always,
            add_defaults_switch e ss d = (t, req, stimes, always) ->
            PS.Empty (stimes ∩ always).
        Proof.
          unfold add_defaults_switch.
          intros * Hadd.
          destruct (add_defaults_branches ss d) as [[[[ss' d'] r] s] a] eqn: E.
          inv Hadd.
          apply PSP.empty_is_empty_2; intro; PS_split; intuition.
        Qed.

        Lemma add_defaults_switch_subset_required:
          forall e t req stimes always,
            add_defaults_switch e ss d = (t, req, stimes, always) ->
            required ⊆ (always ∪ req).
        Proof.
          unfold add_defaults_switch.
          intros * Hadd.
          destruct (add_defaults_branches ss d) as [[[[ss' d'] r] s] a] eqn: E.
          inv Hadd.
          intros x Hin.
          destruct (PSP.In_dec x a), (PSP.In_dec x s); PS_split; intuition.
        Qed.

        Section Inv1.

          Hypothesis IH:
            Forall
              (fun os =>
                 forall t req' stimes always,
                   add_defaults_stmt (or_default d os) = (t, req', stimes, always) ->
                   PS.For_all (fun x => Can_write_in_var x (or_default d os)) (stimes ∪ always)
                   /\ No_Naked_Vars t) ss.

          Lemma add_defaults_branches_inv1:
            forall d' ss' r s a,
              add_defaults_branches ss d = (ss', d', r, s, a) ->
              PS.For_all (fun x => Exists (fun os => Can_write_in_var x (or_default d os)) ss) (s ∪ a)
              /\ Forall (fun os => No_Naked_Vars (or_default d' os)) ss'.
          Proof.
            unfold add_defaults_branches.
            intros * Hadd.
            destruct (add_defaults_stmt d) as [[[d'' r_d] s_d] a_d] eqn: Ed.
            destruct ss as [|os ss'']; simpl.
            - inv Hadd; repeat split; auto.
              intro; PS_split; intros []; contradiction.
            - setoid_rewrite <-fold_left_rev_right in Hadd.
              inversion_clear IH as [|?? IHos IH'].
              apply Forall_rev in IH'.
              setoid_rewrite CommonList.Exists_rev; simpl.
              revert dependent r; revert s a ss'.
              induction (rev ss'') as [|os']; simpl in *; intros.
              + destruct os as [s'|]; simpl in *.
                * destruct (add_defaults_stmt s') as [[[t r_t] s_t] a_t] eqn: Et.
                  inv Hadd; edestruct IHos; eauto; intuition.
                  left; simpl; PS_split; intuition.
                * inv Hadd; edestruct IHos; eauto; intuition.
                  left; simpl; PS_split; intuition.
              + assert (d' = d'') by cases; subst d''.
                inversion_clear IH' as [|?? IHos' IH''].
                destruct (fold_right _ _ _) as [[[ss_l r_l] s_l] aa_l].
                specialize (IHl IH'' _ _ _ _ eq_refl); clear IH'';
                  destruct IHl as (Hcw_l &?).
                destruct os' as [s'|]; simpl in *.
                * destruct (add_defaults_stmt s') as [[[t r_t] s_t] a_t].
                  inv Hadd.
                  edestruct IHos' as (Hcw_s' &?); eauto.
                  split.
                  -- intros x Hin; specialize (Hcw_l x); specialize (Hcw_s' x).
                     PS_split; intuition.
                  -- apply Forall_app; split; eauto.
                * inv Hadd.
                  apply IHos' in Ed as (Hcw_d &?).
                  split.
                  -- intros x Hin; specialize (Hcw_l x); specialize (Hcw_d x).
                     PS_split; intuition.
                  -- apply Forall_app; split; eauto.
          Qed.

          Corollary add_defaults_switch_inv1:
            forall e t req stimes always,
              add_defaults_switch e ss d = (t, req, stimes, always) ->
              PS.For_all (fun x => Can_write_in_var x (Switch e ss d)) (stimes ∪ always)
              /\ No_Naked_Vars t.
          Proof.
            unfold add_defaults_switch.
            intros * Hadd.
            destruct (add_defaults_branches ss d) as [[[[ss' d'] r] s] a] eqn: E.
            apply add_defaults_branches_inv1 in E as (Hcw &?); auto.
            inv Hadd; split.
            - intros x Hin.
              apply Can_write_in_var_Switch, Hcw.
              PS_split; intuition.
            - apply No_Naked_Vars_add_writes; auto using No_Naked_Vars.
          Qed.

        End Inv1.

        Section CanWriteIn.

          Hypothesis IH:
            Forall
              (fun os =>
                 forall t req' st al,
                   add_defaults_stmt (or_default d os) = (t, req', st, al) ->
                   forall x, Can_write_in_var x (or_default d os) <-> Can_write_in_var x t) ss.

          Lemma Can_write_in_add_defaults_branches:
            forall ss' d' r s a,
              add_defaults_branches ss d = (ss', d', r, s, a) ->
              forall x, Forall2 (fun os os' => Can_write_in_var x (or_default d os)
                                       <-> Can_write_in_var x (or_default d' os')) ss ss'.
          Proof.
            intros * Hadd.
            unfold add_defaults_branches in Hadd.
            destruct (add_defaults_stmt d) as [[[d'' r_d] s_d] a_d] eqn: Ed.
            destruct ss as [|os ss'']; simpl in *.
            - inv Hadd; constructor.
            - setoid_rewrite <-fold_left_rev_right in Hadd.
              inversion_clear IH as [|?? IHos IH'].
              setoid_rewrite CommonList.Forall_rev in IH'.
              setoid_rewrite Forall2_rev; simpl.
              revert dependent ss'; revert r s a.
              induction (rev ss'') as [|os']; simpl in *; intros.
              + destruct os as [s'|]; simpl in *.
                * destruct (add_defaults_stmt s') as [[[t' r_t'] s_t'] a_t'] eqn: Et'.
                  inv Hadd; simpl; constructor; eauto.
                * inv Hadd; simpl; constructor; eauto.
              + assert (d' = d'') by cases; subst d''.
                inversion_clear IH' as [|?? IHos' IH].
                destruct (fold_right _ _ _) as [[[ss_l r_l] s_l] aa_l].
                specialize (IHl IH _ _ _ _ eq_refl); clear IH.
                destruct os' as [s'|]; simpl in *.
                * destruct (add_defaults_stmt s') as [[[t r_t] s_t] a_t] eqn: Es'.
                  inv Hadd. rewrite rev_unit.
                  constructor; eauto.
                * inv Hadd. rewrite rev_unit.
                  constructor; eauto.
          Qed.

          Corollary Can_write_in_add_defaults_switch:
            forall e t req stimes always,
              add_defaults_switch e ss d = (t, req, stimes, always) ->
              PS.For_all (fun x => Exists (fun os => Can_write_in_var x (or_default d os)) ss) (stimes ∪ always) ->
              forall x, Can_write_in_var x (Switch e ss d) <-> Can_write_in_var x t.
          Proof.
            intros * Hadd Hcw'.
            unfold add_defaults_switch in Hadd.
            destruct (add_defaults_branches _ _) as [[[[ss' d'] r] s] a] eqn: Hbr.
            intro x; apply Can_write_in_add_defaults_branches with (x := x) in Hbr; auto.
            inv Hadd.
            rewrite Can_write_in_var_Switch; split; intros Hcw.
            - apply Can_write_in_add_writes_mono.
              rewrite Can_write_in_var_Switch.
              clear - Hbr Hcw.
              induction Hbr as [|???? Heq].
              + now inv Hcw.
              + inv Hcw.
                * left; now apply Heq.
                * right; auto.
            - apply Can_write_in_add_writes in Hcw as [Hcw|Hcw].
              + apply Hcw'; PS_split; intuition; auto.
              + inv Hcw.
                take (Exists _ _) and rename it into Hcw.
                clear - Hcw Hbr.
                induction Hbr as [|???? Heq].
                * now inv Hcw.
                * inv Hcw.
                  -- left; now apply Heq.
                  -- right; auto.
          Qed.

        End CanWriteIn.

        Section NoWrite.

          Variable p: program.

          Hypothesis IH:
            Forall
              (fun os =>
                 forall t req' st al me me' ve ve',
                   add_defaults_stmt (or_default d os) = (t, req', st, al) ->
                   stmt_eval p me ve (or_default d os) (me', ve') ->
                   forall x, ~ x ∈ (st ∪ al) -> Env.find x ve' = Env.find x ve) ss.

          Lemma add_defaults_branches_no_write:
            forall ss' d' r s a me me' ve ve',
              add_defaults_branches ss d = (ss', d', r, s, a) ->
              Forall (fun os =>
                stmt_eval p me ve (or_default d os) (me', ve') ->
                forall x, ~ x ∈ (s ∪ a) ->
                     Env.find x ve' = Env.find x ve) ss.
          Proof.
            intros * Hadd.
            cut (a ⊆ s
                 /\ Forall (fun os =>
                             stmt_eval p me ve (or_default d os) (me', ve') ->
                             forall x, ~ x ∈ (s ∪ a) -> Env.find x ve' = Env.find x ve) ss);
              [intros (?&?); auto |].
            unfold add_defaults_branches in Hadd.
            destruct (add_defaults_stmt d) as [[[d'' r_d] s_d] a_d] eqn: Ed.
            destruct ss as [|os ss''].
            - simpl in *; split; auto.
              inv Hadd; reflexivity.
            - setoid_rewrite <-fold_left_rev_right in Hadd.
              inversion_clear IH as [|?? IHos IH'].
              rewrite CommonList.Forall_rev in *; simpl.
              revert dependent ss'; revert dependent s; revert r a.
              induction (rev ss'') as [|os']; simpl in *; intros; auto.
              + destruct os as [s'|]; simpl in *.
                * destruct (add_defaults_stmt s') as [[[t' r_t'] s_t'] a_t'] eqn: Et'.
                  inv Hadd; split.
                  -- intros ??; PS_split; auto.
                  -- constructor; auto; intros.
                     eapply IHos; eauto; PS_split; intuition.
                * inv Hadd; split.
                  -- intros ??; PS_split; auto.
                  -- constructor; auto; intros.
                     eapply IHos; eauto; PS_split; intuition.
              + assert (d' = d'') by cases; subst d''.
                inversion_clear IH' as [|?? IHos' IH].
                destruct (fold_right _ _ _) as [[[ss_l r_l] s_l] aa_l].
                specialize (IHl IH _ _ _ _ eq_refl) as (IHl1 & IHl2).
                rewrite Forall_cons2.
                destruct os' as [s'|]; simpl in *.
                * destruct (add_defaults_stmt s') as [[[t' r_t'] s_t'] a_t'] eqn: Et'.
                  inv Hadd.
                  repeat split.
                  -- intros ??; PS_split; intuition.
                  -- intros; eapply IHos'; eauto; PS_split; intuition.
                  -- eapply Forall_impl; eauto; simpl.
                     intros * IH' ???.
                     apply IH'; auto; PS_split; intuition.
                * inv Hadd.
                  repeat split.
                  -- intros ??; PS_split; intuition.
                  -- intros; eapply IHos'; eauto; PS_split; intuition.
                  -- eapply Forall_impl; eauto; simpl.
                     intros * IH' ???.
                     apply IH'; auto; PS_split; intuition.
          Qed.

          Corollary add_defaults_switch_no_write:
            forall e t me me' ve ve' req stimes always,
              add_defaults_switch e ss d = (t, req, stimes, always) ->
              stmt_eval p me ve (Switch e ss d) (me', ve') ->
              forall x, ~ x ∈ (stimes ∪ always) ->
                   Env.find x ve' = Env.find x ve.
          Proof.
            unfold add_defaults_switch; intros * Hadd Heval x ?.
            destruct (add_defaults_branches ss d) as [[[[ss' d'] r] s] a] eqn: Hbr.
            inv Hadd.
            inv Heval.
            eapply add_defaults_branches_no_write in Hbr; eauto.
            take (nth_error _ _ = _) and rename it into Hin.
            apply nth_error_In in Hin.
            eapply Forall_forall in Hin; eauto; simpl in *.
            apply Hin; eauto.
            PS_split; intuition.
          Qed.

        End NoWrite.

        Section TypingProperties.

          Variables (p : program)
                    (insts : list (ident * ident))
                    (mems  : list (ident * type))
                    (vars  : list (ident * type)).

          Hypothesis wf_vars_tyenv:
            (forall x ty, In (x, ty) vars <-> type_of_var x = Some ty).

          Hypothesis vars_types:
            forall x ty,
              In (x, ty) vars -> wt_type (types p) ty.

          Lemma wf_vars_tyenv':
            forall x, InMembers x vars <-> type_of_var x <> None.
          Proof.
            split; intro HH.
            - apply InMembers_In in HH as (ty, HH).
              apply wf_vars_tyenv in HH. rewrite HH. discriminate.
            - apply not_None_is_Some in HH as (ty, HH).
              apply wf_vars_tyenv in HH. eauto using In_InMembers.
          Qed.

          Lemma add_writes_wt':
            forall W s,
              wt_stmt p insts mems vars (add_writes W s) ->
              wt_stmt p insts mems vars s.
          Proof.
            intros W.
            unfold add_writes. setoid_rewrite PS.fold_spec.
            generalize (PS.elements W); clear W.
            intro ws. induction ws as [|w ws IH]; simpl; auto.
            intros s Hwws. apply IH in Hwws.
            unfold add_write in Hwws.
            destruct (type_of_var w) as [[]|]; auto; now inv Hwws.
          Qed.

          Lemma add_writes_wt:
            forall W s,
              PS.For_all (fun x => type_of_var x <> None) W ->
              (wt_stmt p insts mems vars s <->
               wt_stmt p insts mems vars (add_writes W s)).
          Proof.
            intros W.
            unfold add_writes. setoid_rewrite PS.fold_spec.
            setoid_rewrite PS_For_all_Forall.
            generalize (PS.elements W); clear W.
            intro ws. induction ws as [|w ws IH]; simpl. reflexivity.
            intros s Hwws.
            inversion_clear Hwws as [|? ? Hw Hws].
            rewrite <-IH; auto.
            apply not_None_is_Some in Hw as (ty & Hw).
            unfold add_write. rewrite Hw.
            apply wf_vars_tyenv in Hw.
            split; intro HH.
            - destruct ty.
              + econstructor; eauto; econstructor; simpl; eauto using wt_exp; rewrite ctype_init_ctype; auto.
              + eapply vars_types in Hw as Hwt. inv Hwt.
                repeat (econstructor; eauto).
            - destruct ty; now inversion HH.
          Qed.

          Section WT.

            Hypothesis IHss:
              Forall
                (or_default_with True (fun s =>
                                      forall t req' st al,
                                        add_defaults_stmt s = (t, req', st, al) ->
                                        wt_stmt p insts mems vars s ->
                                        wt_stmt p insts mems vars t
                                        /\ PS.For_all (fun x => InMembers x vars) st
                                        /\ PS.For_all (fun x => InMembers x vars) al
                                        /\ PS.For_all (fun x => InMembers x vars) req')) ss.

            Hypothesis IHd:
              forall t req' st al,
                add_defaults_stmt d = (t, req', st, al) ->
                wt_stmt p insts mems vars d ->
                wt_stmt p insts mems vars t
                /\ PS.For_all (fun x => InMembers x vars) st
                /\ PS.For_all (fun x => InMembers x vars) al
                /\ PS.For_all (fun x => InMembers x vars) req'.

            Lemma add_defaults_branches_wt:
              forall ss' d' r s a,
                add_defaults_branches ss d = (ss', d', r, s, a) ->
                wt_stmt p insts mems vars d ->
                Forall (or_default_with True (wt_stmt p insts mems vars)) ss ->
                wt_stmt p insts mems vars d'
                /\ Forall (or_default_with True (wt_stmt p insts mems vars)) ss'
                /\ PS.For_all (fun x => InMembers x vars) s
                /\ PS.For_all (fun x => InMembers x vars) a
                /\ PS.For_all (fun x => InMembers x vars) r.
            Proof.
              intros * Hadd WTd WTss.
              unfold add_defaults_branches in Hadd.
              destruct (add_defaults_stmt d) as [[[d'' r_d] s_d] a_d] eqn: Ed.
              edestruct IHd as (?&?&?&?); eauto; clear IHd Ed.
              destruct ss as [|os ss''].
              - simpl in *; inv Hadd; repeat split; auto using PS_For_all_empty.
              - setoid_rewrite <-fold_left_rev_right in Hadd.
                inversion_clear IHss as [|?? IHos IH'].
                rewrite CommonList.Forall_rev in *.
                simpl in *.
                revert dependent ss'; revert dependent s; revert r a.
                induction (rev ss'') as [|os']; simpl in *; intros; auto.
                + destruct os as [s'|]; simpl in *.
                  * destruct (add_defaults_stmt s') as [[[t' r_t'] s_t'] a_t'] eqn: Et'.
                    inv Hadd.
                    edestruct IHos as (?&?&?&?); eauto;
                      repeat split; auto.
                    -- inv WTss; auto.
                    -- simpl; constructor; auto.
                    -- apply PS_For_all_union; auto.
                  * inv Hadd.
                    repeat split; auto.
                    apply PS_For_all_union; auto.
                + assert (d' = d'') by cases; subst d''.
                  inversion_clear IH' as [|?? IHos' IH].
                  destruct (fold_right _ _ _) as [[[ss_l r_l] s_l] aa_l].
                  inversion_clear WTss as [|?? WTos' WTss'].
                  specialize (IHl WTss' IH _ _ _ _ eq_refl) as (?&?&?&?&?).
                  destruct os' as [s'|]; simpl in *.
                  * destruct (add_defaults_stmt s') as [[[t' r_t'] s_t'] a_t'] eqn: Et'.
                    inv Hadd.
                    edestruct IHos' as (?&?&?&?); eauto;
                      repeat split; auto.
                    -- rewrite rev_app_distr, Forall_app; split; auto; simpl.
                       constructor; auto.
                    -- repeat apply PS_For_all_union; auto.
                    -- apply PS_For_all_inter; auto.
                    -- apply PS_For_all_union; auto.
                  * inv Hadd.
                    repeat split; auto.
                    -- rewrite rev_app_distr, Forall_app; split; auto; simpl.
                       constructor; auto.
                    -- repeat apply PS_For_all_union; auto.
                    -- apply PS_For_all_inter; auto.
                    -- apply PS_For_all_union; auto.
            Qed.

            Corollary add_defaults_switch_wt:
              forall e t req stimes always,
                add_defaults_switch e ss d = (t, req, stimes, always) ->
                wt_stmt p insts mems vars (Switch e ss d) ->
                wt_stmt p insts mems vars t
                /\ PS.For_all (fun x => InMembers x vars) stimes
                /\ PS.For_all (fun x => InMembers x vars) always
                /\ PS.For_all (fun x => x ∈ required \/ InMembers x vars) req.
            Proof.
              intros * Hadd WT.
              inv WT.
              unfold add_defaults_switch in Hadd.
              destruct (add_defaults_branches ss d) as [[[[ss' d'] r] s] a] eqn: Hbr.
              inv Hadd.
              pose proof Hbr as Len; apply add_defaults_branches_length in Len.
              apply add_defaults_branches_wt in Hbr as (?&?&?&?&?); auto.
              - repeat split.
                + rewrite <-add_writes_wt.
                  * econstructor; eauto.
                    -- intuition.
                    -- intros * Hin; eapply Forall_forall in Hin; eauto; auto.
                  * setoid_rewrite <- wf_vars_tyenv'.
                    apply PS_For_all_inter, PS_For_all_diff; auto.
                + repeat apply PS_For_all_diff; auto.
                + apply PS_For_all_union; auto; apply PS_For_all_inter; auto.
                + repeat apply PS_For_all_diff; auto; apply PS_For_all_union; auto;
                    intros ??; auto; PS_split; intuition.
              - apply Forall_forall; intros os Hin.
                destruct os; simpl; auto.
            Qed.

          End WT.

          Section Inv2.

            Hypothesis IH:
              Forall
                (fun os =>
                   wt_stmt p insts mems vars (or_default d os) ->
                   forall t me me' ve ve',
                     stmt_eval p me ve t (me', ve') ->
                     forall req' st al,
                       add_defaults_stmt (or_default d os) = (t, req', st, al) ->
                       PS.For_all (fun x => Env.In x ve) req' ->
                       (forall x, ~ x ∈ (st ∪ al) -> Env.find x ve' = Env.find x ve)
                       /\ PS.For_all (fun x => Env.In x ve') al) ss.

            Lemma add_defaults_branches_inv2:
              forall ss' d' r s a me me' ve ve',
                add_defaults_branches ss d = (ss', d', r, s, a) ->
                Forall (fun os => wt_stmt p insts mems vars (or_default d os)) ss ->
                PS.For_all (fun x => Env.In x ve) r ->
                Forall (fun os =>
                          stmt_eval p me ve (or_default d' os) (me', ve') ->
                          (forall x, ~ x ∈ (s ∪ a) ->
                                Env.find x ve' = Env.find x ve)
                          /\ PS.For_all (fun x => Env.In x ve') a) ss'.
            Proof.
              intros * Hadd WTss Hr.
              cut (a ⊆ s
                   /\ Forall (fun os =>
                               stmt_eval p me ve (or_default d' os) (me', ve') ->
                               (forall x, ~ x ∈ (s ∪ a) -> Env.find x ve' = Env.find x ve)
                               /\ PS.For_all (fun x => Env.In x ve') a) ss');
                [intros (?&?); auto |].
              unfold add_defaults_branches in Hadd.
              destruct (add_defaults_stmt d) as [[[d'' r_d] s_d] a_d] eqn: Ed.
              destruct ss as [|os ss''].
              - inv Hadd; split; auto.
                reflexivity.
              - setoid_rewrite <-fold_left_rev_right in Hadd.
                inversion_clear IH as [|?? IHos IH'].
                rewrite CommonList.Forall_rev in *; simpl in *.
                revert dependent ss'; revert dependent s; revert dependent r; revert a.
                induction (rev ss'') as [|os']; simpl in *; intros; auto.
                + destruct os as [s'|]; simpl in *.
                  * destruct (add_defaults_stmt s') as [[[t' r_t'] s_t'] a_t'] eqn: Et'.
                    inv Hadd; simpl; split.
                    -- intros ??; PS_split; auto.
                    -- constructor; auto.
                       intros; edestruct IHos; eauto.
                       ++ inv WTss; auto.
                       ++ PS_split; intuition.
              * inv Hadd; simpl; split.
                -- intros ??; PS_split; auto.
                -- constructor; auto.
                   intros; edestruct IHos; eauto.
                   ++ inv WTss; auto.
                   ++ PS_split; intuition.
              + assert (d' = d'') by cases; subst d''.
                inversion_clear IH' as [|?? IHos' IH].
                destruct (fold_right _ _ _) as [[[ss_l r_l] s_l] aa_l].
                inversion_clear WTss as [|?? WTos' WTss'].
                assert (PS.For_all (fun x : PS.elt => Env.In x ve) r_l) as Hr_l.
                { destruct os' as [s'|]; simpl in *.
                  - destruct (add_defaults_stmt s') as [[[t' r_t'] s_t'] a_t'].
                    inv Hadd; intros ??; apply Hr; PS_split; auto.
                  - inv Hadd; intros ??; apply Hr; PS_split; auto.
                }
                specialize (IHl WTss' IH _ _ Hr_l _ _ eq_refl) as (IHl1 & IHl2).
                destruct os' as [s'|]; simpl in *.
                * destruct (add_defaults_stmt s') as [[[t' r_t'] s_t'] a_t'] eqn: Et'.
                  inv Hadd.
                  rewrite rev_app_distr, Forall_app; repeat split.
                  -- intros ??; PS_split; intuition.
                  -- simpl; constructor; auto.
                     intros; edestruct IHos'; eauto.
                     ++ intros ??; apply Hr; PS_split; auto.
                     ++ PS_split; intuition.
                        rewrite PSP.inter_sym; apply PS_For_all_inter; auto.
                  -- eapply Forall_impl; eauto; simpl; intros.
                     PS_split; intuition.
                     apply PS_For_all_inter; auto.
              * inv Hadd.
                rewrite rev_app_distr, Forall_app; repeat split.
                -- intros ??; PS_split; intuition.
                -- simpl; constructor; auto.
                   intros; edestruct IHos'; eauto.
                   ++ intros ??; apply Hr; PS_split; auto.
                   ++ PS_split; intuition.
                      rewrite PSP.inter_sym; apply PS_For_all_inter; auto.
              -- eapply Forall_impl; eauto; simpl; intros.
                 PS_split; intuition.
                 apply PS_For_all_inter; auto.
            Qed.

            Lemma add_defaults_switch_inv2:
              forall e t req stimes always me me' ve ve',
                add_defaults_switch e ss d = (t, req, stimes, always) ->
                wt_stmt p insts mems vars (Switch e ss d) ->
                stmt_eval p me ve t (me', ve') ->
                PS.For_all (fun x => Env.In x ve) req ->
                PS.For_all (fun x => InMembers x vars) always ->
                (forall x, ~ x ∈ (stimes ∪ always) -> Env.find x ve' = Env.find x ve)
                /\ PS.For_all (fun x => Env.In x ve') always.
            Proof.
              intros * Hadd WT Heval Hreq Hal.
              unfold add_defaults_switch in Hadd.
              destruct (add_defaults_branches ss d) as [[[[ss' d'] r] s] a] eqn: Hbr.
              inv Hadd.
              apply stmt_eval_add_writes_split in Heval as (meW & veW & HevalW & Heval).
              pose proof (stmt_eval_add_writes_Skip_other _ _ _ _ _ _ HevalW) as HW.
              inv Heval.
              assert (PS.For_all (fun x => type_of_var x <> None) ((s \ a) ∩ required))
                by (setoid_rewrite <-wf_vars_tyenv'; intros ??; PS_split; intuition).
              eapply add_defaults_branches_inv2 in Hbr; eauto.
              - take (nth_error _ _ = _) and rename it into Hin;
                  apply nth_error_In in Hin.
                eapply Forall_forall in Hin; eauto; simpl in *.
                take (stmt_eval _ _ _ _ (me', ve')) and specialize (Hin it) as (Hve & Hal').
                split.
                + intros; rewrite Hve, HW; auto; PS_split; intuition.
                + apply PS_For_all_union; auto.
                  intros ??.
                  destruct (PSP.In_dec x a); auto.
                  eapply stmt_eval_mono; eauto.
                  eapply stmt_eval_add_writes; eauto.
                  PS_split; intuition.
              - inversion_clear WT as [| |???????? Hwtd Hwtss| | | |].
                apply Forall_forall; intros os Hin.
                destruct os; auto.
              - intros x Hin.
                destruct (PSP.In_dec x ((s \ a) ∩ required)).
                + eapply stmt_eval_add_writes in HevalW; eauto.
                + eapply stmt_eval_mono; eauto; intuition.
            Qed.

          End Inv2.

          Section Correct.

            Definition in1_notin2 xs1 xs2 (ve1 ve2 : Env.t value) :=
              (forall x, x ∈ xs1 -> Env.In x ve1)
              /\ (forall x, x ∈ xs2 -> ~Env.In x ve2).

            Lemma in1_notin2_infer:
              forall ve1 ve2 S1 S2 Z1 Z2,
                in1_notin2 S1 S2 ve1 ve2 ->
                (forall x, x ∈ Z1 -> x ∈ S1) ->
                (forall x, x ∈ Z2 -> x ∈ S2) ->
                in1_notin2 Z1 Z2 ve1 ve2.
            Proof.
              intros * (?, ?) ? ?; split; auto.
            Qed.
            Definition all_in1 (xs : list (ident * type)) (ve1 ve2 : Env.t value) :=

              (forall x, InMembers x xs <-> Env.In x ve1)
              /\ (forall x, Env.In x ve2 -> InMembers x xs).

            Variable p': program.

            Hypothesis IH:
              Forall
                (fun os =>
                   forall t rq' st al,
                     add_defaults_stmt (or_default d os) = (t, rq', st, al) ->
                     No_Overwrites (or_default d os) ->
                     wt_stmt p insts mems vars (or_default d os) ->
                     stmt_refines p p' (in1_notin2 rq' (st ∪ al)) t (or_default d os)) ss.

            Hypothesis Hpr: program_refines (fun _ _ => all_in1) p p'.

            Lemma add_defaults_branches_correct:
              forall r s a ss' d' ,
                add_defaults_branches ss d = (ss', d', r, s, a) ->
                Forall (fun os => No_Overwrites (or_default d os)) ss ->
                Forall (or_default_with True (wt_stmt p insts mems vars)) ss ->
                wt_stmt p insts mems vars d ->
                Forall2 (fun os os' =>
                           stmt_refines p p'
                                        (in1_notin2 r (s ∪ a))
                                        (or_default d' os') (or_default d os)) ss ss'.
            Proof.
              intros * Hadd NOOss WTss WTd.
              cut (a ⊆ s
                   /\ Forall2 (fun os os' => stmt_refines p p'
                                                      (in1_notin2 r (s ∪ a))
                                                      (or_default d' os') (or_default d os)) ss ss');
                [intros (?&?); auto |].
              unfold add_defaults_branches in Hadd.
              destruct (add_defaults_stmt d) as [[[d'' r_d] s_d] a_d] eqn: Ed.
              destruct ss as [|os ss''].
              - inv Hadd; split; auto.
                reflexivity.
              - setoid_rewrite <-fold_left_rev_right in Hadd.
                inversion_clear IH as [|?? IHos IH'].
                rewrite CommonList.Forall_rev in NOOss, WTss, IH'.
                rewrite Forall2_rev; simpl in *.
                revert dependent ss'; revert dependent s; revert dependent r; revert a.
                induction (rev ss'') as [|os']; simpl in *; intros; auto.
                + inversion_clear NOOss as [|?? NOOs]; inversion_clear WTss as [|?? WTs].
                  destruct os as [s'|]; simpl in *.
                  * destruct (add_defaults_stmt s') as [[[t' r_t'] s_t'] a_t'] eqn: Et'.
                    inv Hadd; simpl; split.
                    -- intros ??; PS_split; intuition.
                    -- constructor; auto.
                       specialize (IHos _ _ _ _ eq_refl NOOs WTs).
                       eapply stmt_refines_strengthen; eauto.
                       intros; eapply in1_notin2_infer; eauto.
                       PS_split; intuition.
              * inv Hadd; simpl; split.
                -- intros ??; PS_split; intuition.
                -- constructor; auto.
                   eapply IHos in Ed; eauto.
                   eapply stmt_refines_strengthen; eauto.
                   intros; eapply in1_notin2_infer; eauto.
                   PS_split; intuition.
              + assert (d' = d'') by cases; subst d''.
                inversion_clear IH' as [|?? IHos' IH].
                destruct (fold_right _ _ _) as [[[ss_l r_l] s_l] aa_l].
                inversion_clear WTss as [|?? WTos' WTss'];
                  inversion_clear NOOss as [|?? NOOos' NOOss'].
                specialize (IHl NOOss' WTss' IH _ _ _ _ eq_refl) as (IHl1 & IHl2).
                destruct os' as [s'|]; simpl in *.
                * destruct (add_defaults_stmt s') as [[[t' r_t'] s_t'] a_t'] eqn: Et'.
                  inv Hadd; split.
                  -- intros ??; PS_split; intuition.
                  -- rewrite rev_app_distr; simpl.
                     constructor; auto.
                     ++ specialize (IHos' _ _ _ _ eq_refl NOOos' WTos').
                        eapply stmt_refines_strengthen; eauto.
                        intros; eapply in1_notin2_infer; eauto;
                          PS_split; intuition.
                     ++ eapply Forall2_impl_In; eauto; simpl; intros.
                        eapply stmt_refines_strengthen; eauto.
                        intros; eapply in1_notin2_infer; eauto;
                          PS_split; intuition.
                * inv Hadd; split.
                  -- intros ??; PS_split; intuition.
                  -- rewrite rev_app_distr; simpl.
                     constructor; auto.
                     ++ eapply IHos' in Ed; eauto.
                        eapply stmt_refines_strengthen; eauto.
                        intros; eapply in1_notin2_infer; eauto;
                          PS_split; intuition.
                     ++ eapply Forall2_impl_In; eauto; simpl; intros.
                        eapply stmt_refines_strengthen; eauto.
                        intros; eapply in1_notin2_infer; eauto;
                          PS_split; intuition.
            Qed.

            Lemma stmt_eval_add_writes_Skip:
              forall me w ve0' ve0,
                ve0 ⊑ ve0' ->
                PS.For_all (fun x => ~Env.In x ve0) w ->
                PS.For_all (fun x => InMembers x vars) w ->
                exists ve1',
                  ve0 ⊑ ve1'
                  /\ stmt_eval p me ve0' (add_writes w Skip) (me, ve1')
                  /\ (forall x, Env.In x ve0' -> Env.In x ve1')
                  /\ PS.For_all (fun x => Env.In x ve1') w.
            Proof.
              intros me w.
              unfold add_writes.
              setoid_rewrite PSP.fold_spec_right.
              setoid_rewrite PS_For_all_Forall.
              setoid_rewrite (Permutation.Permutation_rev (PS.elements w)) at -3.
              remember (rev (PS.elements w)) as ws.
              setoid_rewrite <-Heqws; clear Heqws w.
              induction ws as [|w ws IHws]; eauto using stmt_eval.
              intros ve0' ve0 Henv Hni Hm.
              inversion_clear Hni as [|? ? Hniw Hniws].
              inversion_clear Hm as [|? ? Hmw Hmws].
              eapply wf_vars_tyenv', not_None_is_Some in Hmw as (wty & Hwty); eauto.
              simpl. unfold add_write at 1. rewrite Hwty.
              destruct wty.
              - apply (Env.refines_add_right _ _ _ w (Vscalar (sem_cconst (init_ctype c))))
                  with (2:=Hniw) in Henv.
                apply IHws with (1:=Henv) (2:=Hniws) in Hmws
                  as (ve1' & Henv'' & Heval' & Hinin' & Hfa').
                exists ve1'. repeat (try apply Forall_cons2; split; eauto).
                repeat econstructor; eauto. 2:eauto with env.
                intros; apply Hinin', Env.Props.P.F.add_in_iff; auto.
              - apply (Env.refines_add_right _ _ _ w (Venum 0))
                  with (2:=Hniw) in Henv.
                apply IHws with (1:=Henv) (2:=Hniws) in Hmws
                  as (ve1' & Henv'' & Heval' & Hinin' & Hfa').
                exists ve1'. repeat (try apply Forall_cons2; split; eauto).
                repeat econstructor; eauto. 2:eauto with env.
                intros; apply Hinin', Env.Props.P.F.add_in_iff; auto.
            Qed.

            Lemma add_defauts_switch_correct:
              forall t req st al e,
                add_defaults_switch e ss d = (t, req, st, al) ->
                No_Overwrites (Switch e ss d) ->
                wt_stmt p insts mems vars (Switch e ss d) ->
                PS.For_all (fun x => InMembers x vars) al ->
                stmt_refines p p' (in1_notin2 req (st ∪ al)) t (Switch e ss d).
            Proof.
              intros * Hadd NOO WT Hal.
              unfold add_defaults_switch in Hadd.
              destruct (add_defaults_branches ss d) as [[[[ss' d'] r] s] a] eqn: Hbr.
              inv Hadd.
              inv NOO; inv WT.
              eapply add_defaults_branches_correct in Hbr; eauto.
              - intros me ve1 ve2 me' ve2' Hpre Henv Heval.
                inv Heval.
                eapply nth_error_Forall2 in Hbr as (os' &?& IHos'); eauto.
                edestruct stmt_eval_add_writes_Skip
                  with (me := me) (w := (s \ a) ∩ required)
                  as (ve3' & Henv3' & Heval3' & Hmono3 & Hin3'); eauto.
                + intros ??; apply Hpre.
                  PS_split; intuition.
                + intros ??; PS_split; intuition.
                + edestruct IHos' as (ve4' &?&?); eauto.
                  * split.
                    -- intros x Hrq.
                       destruct (PSP.In_dec x ((s \ a) ∩ required)) as [Hw|Hnw].
                       ++ now apply PS_In_Forall with (1:=Hin3') (2:=Hw).
                       ++ apply Hmono3, Hpre; PS_split; intuition.
                    -- intros; apply Hpre.
                       destruct (PSP.In_dec x required), (PSP.In_dec x a);
                         PS_split; intuition.
                  * exists ve4'; split; auto.
                    apply stmt_eval_add_writes_split.
                    exists me, ve3'; split; auto.
                    econstructor; eauto using exp_eval_refines.
              - apply Forall_forall; intros [|] ?; simpl; auto.
            Qed.

          End Correct.

        End TypingProperties.

      End Properties.

    End AddDefaultsSwitch.

    Fixpoint add_defaults_stmt (required: PS.t) (s: stmt) : stmt * PS.t * PS.t * PS.t :=
      match s with
      | Skip => (s, required, ∅, ∅)
      | Assign x e => (s, PS.remove x required, ∅, PS.singleton x)
      | AssignSt x e => (s, required, ∅, ∅)
      | Call xs f o m es =>
        let (es', required') := fold_right add_valid
                                           ([], ps_removes xs required) es
        in (Call xs f o m es', required', ∅, PSP.of_list xs)
      | ExternCall y f fty es => (s, PS.remove y required, ∅, PS.singleton y)
      | Comp s1 s2 =>
        let '(t2, required2, sometimes2, always2) := add_defaults_stmt required s2 in
        let '(t1, required1, sometimes1, always1) := add_defaults_stmt required2 s1 in
        (Comp t1 t2,
         required1,
         (sometimes1 \ always2) ∪ (sometimes2 \ always1),
         always1 ∪ always2)

      | Switch e [Some s1; Some s2] _
      | Switch e [Some s1; None] s2
      | Switch e [None; Some s2] s1 =>
        add_defaults_ite (add_defaults_stmt ∅) required e s1 s2

      | Switch e ss d =>
        add_defaults_switch (add_defaults_stmt ∅) required e ss d
      end.

  End AddDefaults.

  Definition add_defaults_method (m: method): method :=
    match m with
      mk_method name ins vars outs body nodup good =>
      mk_method name ins vars outs
         (let tyenv := fun x => Env.find x
                (Env.adds' outs (Env.adds' vars (Env.from_list ins))) in
          let '(body', required, sometimes, always) :=
              add_defaults_stmt tyenv (PSP.of_list (map fst outs)) body in
          add_writes tyenv (ps_removes (map fst ins) required) body')
         nodup good
    end.

  Lemma add_defaults_method_m_name:
    forall m,
      (add_defaults_method m).(m_name) = m.(m_name).
  Proof. now destruct m. Qed.

  Lemma add_defaults_method_m_in:
    forall m, (add_defaults_method m).(m_in) = m.(m_in).
  Proof. now destruct m. Qed.

  Lemma add_defaults_method_m_out:
    forall m, (add_defaults_method m).(m_out) = m.(m_out).
  Proof. now destruct m. Qed.

  Lemma add_defaults_method_m_vars:
    forall m, (add_defaults_method m).(m_vars) = m.(m_vars).
  Proof. now destruct m. Qed.

  Program Definition add_defaults_class (c: class): class :=
    match c with
      mk_class name mems objs methods nodup nodupm cgood =>
      mk_class name mems objs (map add_defaults_method methods) nodup _ cgood
    end.
  Next Obligation.
    rewrite map_map. now setoid_rewrite add_defaults_method_m_name.
  Qed.

  Global Program Instance add_default_class_transform_unit: TransformUnit class class :=
    { transform_unit := add_defaults_class }.
  Next Obligation.
    intros; unfold add_defaults_class; cases.
  Defined.

  Global Program Instance add_default_class_transform_state_unit: TransformStateUnit class class.
  Next Obligation.
    unfold add_defaults_class; cases.
  Defined.

  Definition add_defaults : program -> program := transform_units.

  Lemma find_method_add_defaults_method:
    forall n ms m,
      find_method n ms = Some m ->
      find_method n (map add_defaults_method ms) = Some (add_defaults_method m).
  Proof.
    induction ms as [|m ms' IH]. discriminate.
    simpl. setoid_rewrite add_defaults_method_m_name.
    destruct (ident_eqb m.(m_name) n); auto.
    now inversion_clear 1.
  Qed.

  Lemma find_method_map_add_defaults_method':
    forall n ms fm,
      find_method n (map add_defaults_method ms) = Some fm
      -> exists fm',
        find_method n ms = Some fm' /\ fm = add_defaults_method fm'.
  Proof.
    induction ms as [|m ms' IH]. discriminate.
    simpl. setoid_rewrite add_defaults_method_m_name.
    destruct (ident_eqb m.(m_name) n); auto.
    inversion_clear 1; eauto.
  Qed.

  Lemma find_method_map_add_defaults_method:
    forall n c,
      find_method n (map add_defaults_method c.(c_methods))
      = find_method n (add_defaults_class c).(c_methods).
  Proof. now destruct c. Qed.

  Lemma add_defaults_class_c_name:
    forall c, (add_defaults_class c).(c_name) = c.(c_name).
  Proof. pose proof transform_unit_conservative_name; simpl in *; auto. Qed.

  Lemma add_defaults_class_c_objs:
    forall c, (add_defaults_class c).(c_objs) = c.(c_objs).
  Proof. now destruct c. Qed.

  Lemma add_defaults_class_c_mems:
    forall c, (add_defaults_class c).(c_mems) = c.(c_mems).
  Proof. now destruct c. Qed.

  Lemma find_class_add_defaults_class:
    forall p n c p',
      find_class n p = Some (c, p') ->
      find_class n (add_defaults p)
      = Some (add_defaults_class c, add_defaults p').
  Proof.
    intros * Find; now apply find_unit_transform_units_forward in Find.
  Qed.

  Corollary find_class_add_defaults_class_not_None:
    forall n p,
      find_class n p <> None ->
      find_class n (add_defaults p) <> None.
  Proof.
    intros n p Hfind.
    apply not_None_is_Some in Hfind as ((c & p') & Hfind).
    apply find_class_add_defaults_class in Hfind.
    now rewrite Hfind.
  Qed.

  Lemma simplify_write_sets:
    forall w w1 w2 al1 al2 st1 st2 rq,
      w1 = (al2 ∩ rq) \ (al1 ∩ rq) ->
      w2 = (al1 ∩ rq) \ (al2 ∩ rq) ->
      w = ((st1 ∩ rq) \ w1) ∪ ((st2 ∩ rq) \ w2) ->
      PS.Equal ((((st1 \ w1)
                    ∪ (st2 \ w2)
                    ∪ ((al1 ∪ w1) \ (al2 ∪ w2))
                    ∪ (al2 ∪ w2) \ (al1 ∪ w1)) \ w)
                  ∪ ((al1 ∪ w1) ∩ al2 ∪ w2) ∪ w)
               (w ∪ w1 ∪ w2 ∪ al1 ∪ al2 ∪ st1 ∪ st2).
  Proof.
    intros. intro x.
    rewrite (PSP.union_sym _ w), <-(PSP.union_assoc _ w), PS_union_diff_same.
    split; intro HH. now PS_split; tauto.
    destruct (PSP.In_dec x (al2 ∪ w2));
      destruct (PSP.In_dec x (al1 ∪ w1)).
    - PS_split; tauto.
    - PS_split; tauto.
    - PS_split; tauto.
    - PS_split; tauto.
  Qed.

  (** ** Basic lemmas around [add_defaults_class] and [add_defaults_method]. *)

  Lemma add_defaults_class_find_method:
    forall f c,
      find_method f (add_defaults_class c).(c_methods)
      = option_map (add_defaults_method) (find_method f c.(c_methods)).
  Proof.
    intros f c. destruct c. simpl.
    rewrite find_method_map; auto.
    now intro m; destruct m.
  Qed.

  Lemma In_snd_fold_right_add_valid:
    forall s es xs,
      s ⊆ (snd (fold_right add_valid (xs, s) es)).
  Proof.
    intros ??? x Hin.
    induction es as [|e es IH]; auto.
    simpl. unfold add_valid at 1.
    rewrite (surjective_pairing (fold_right _ _ _)).
    destruct e; simpl; auto. rewrite PS.add_spec.
    edestruct (equiv_dec x); [now left; eauto|auto].
  Qed.

  Definition add_valid' e := match e with Var x ty => Valid x ty | _ => e end.

  Lemma add_valid_add_valid':
    forall es S es',
      fst (fold_right add_valid (es', S) es) = map add_valid' es ++ es'.
  Proof.
    induction es as [|e es IH]; auto.
    simpl. intros S xs'.
    destruct e; simpl; rewrite IH; auto.
  Qed.

  Lemma Forall2_exp_eval_refines_with_valid:
    forall me ve1 ve2 es vos,
      ve2 ⊑ ve1 ->
      Forall (fun e => match e with Var x _ => Env.In x ve1 | _ => True end) es ->
      Forall2 (exp_eval me ve2) es vos ->
      exists vos',
        Forall2 (exp_eval me ve1) (map add_valid' es) vos'
        /\ Forall2 (fun vo vo' => forall v, vo = Some v -> vo' = Some v) vos vos'.
  Proof.
    intros me ve1 ve2 es vos Henv Hvar Hvos.
    induction Hvos as [|e vo es vos He Hfa IH].
    now setoid_rewrite Forall2_map_1; eauto.
    apply Forall_cons2 in Hvar as (Hvar & Hvars).
    apply exp_eval_refines' with (1:=Henv) in He as (vo' & Heval & Hvo').
    destruct IH as (vos' & Hevals & Hvos'); auto.
    destruct e; simpl; eauto using Forall2_cons.
    assert (exists v', vo' = Some v') as (v' & Hv')
        by now inv Heval; rewrite Env.In_find in Hvar.
    exists (vo'::vos'). subst vo'; split; auto.
    inv Heval; constructor; eauto using exp_eval.
    take (Env.find _ _ = _) and rewrite it; eauto using exp_eval.
  Qed.


  Lemma add_defaults_stmt_switch_spec:
    forall tyenv req e ss d t req' stimes always,
      add_defaults_stmt tyenv req (Switch e ss d) = (t, req', stimes, always) ->
      (exists s1 s2,
          (ss = [Some s1; Some s2]
           \/ ss = [Some s1; None] /\ d = s2
           \/ ss = [None; Some s2] /\ d = s1)
          /\ add_defaults_ite tyenv (add_defaults_stmt tyenv ∅) req e s1 s2 = (t, req', stimes, always))
      \/
      add_defaults_switch tyenv (add_defaults_stmt tyenv ∅) req e ss d = (t, req', stimes, always).
  Proof.
    intros * H; inv H.
    cases; left; do 2 eexists; eauto.
  Qed.

  Lemma add_defaults_stmt_inv1:
    forall tyenv s t req req' stimes always,
      add_defaults_stmt tyenv req s = (t, req', stimes, always) ->
      PS.Empty (stimes ∩ always)
      /\ req ⊆ (always ∪ req')
      /\ PS.For_all (fun x => Can_write_in_var x s) (stimes ∪ always)
      /\ No_Naked_Vars t.
  Proof.
    unfold PS.For_all.
    induction s as [| |??? IH| |ys clsid o f es| |] using stmt_ind2;
      intros t rq rq' st al Hadd.
    - (* * Assign i e *)
      inv Hadd.
      split; [now intuition|repeat split]; auto with obcinv.
      + intros y Hin. rewrite PS.union_spec.
        edestruct (equiv_dec y) as [He|Hne]; eauto using PSF.remove_2.
        now rewrite He, PS.singleton_spec; auto.
      + setoid_rewrite PS.union_spec.
        intros y [Hin|Hin]; try not_In_empty.
        apply PSF.singleton_iff in Hin; subst; auto with obcinv.

    - (* * AssignSt i e *)
      inv Hadd.
      setoid_rewrite PSF.empty_iff; intuition.

    - apply add_defaults_stmt_switch_spec in Hadd as [(s1 & s2 & E & Hadd)|Hadd].
      (* if-then-else's *)
      + unfold add_defaults_ite in Hadd.
        set (defs1 := add_defaults_stmt tyenv ∅ s1) in *.
        destruct defs1 as [[[t1 rq1] st1] al1] eqn: E1.
        set (defs2 := add_defaults_stmt tyenv ∅ s2) in *.
        destruct defs2 as [[[t2 rq2] st2] al2] eqn: E2.

        remember ((al2 ∩ rq) \ (al1 ∩ rq)) as w1.
        remember ((al1 ∩ rq) \ (al2 ∩ rq)) as w2.
        remember (((st1 ∩ rq) \ w1) ∪ ((st2 ∩ rq) \ w2)) as w.
        assert (forall x, x ∈ w1 <-> x ∈ al2 /\ x ∈ rq /\ ~x ∈ al1) as Hw1
            by (subst w1; clear; PS_split; intuition).
        assert (forall x, x ∈ w2 <-> x ∈ al1 /\ x ∈ rq /\ ~x ∈ al2) as Hw2
            by (subst w2; clear; PS_split; intuition).

        injection Hadd; clear Hadd; intros; subst al st rq' t.
        subst defs1 defs2.
        assert (PS.Empty (st1 ∩ al1)
                /\ (forall x, x ∈ (st1 ∪ al1) -> Can_write_in_var x s1)
                /\ No_Naked_Vars t1
                /\ PS.Empty (st2 ∩ al2)
                /\ (forall x, x ∈ (st2 ∪ al2) -> Can_write_in_var x s2)
                /\ No_Naked_Vars t2) as [H1A [H1C [H1E [H2A [H2C H2E]]]]]
          by (destruct E as [|[[]|[]]]; subst;
                inversion_clear IH as [|?? IH1 IH']; inversion_clear IH' as [|?? IH2 IH'']; clear IH'';
                apply IH1 in E1; apply IH2 in E2; intuition).
        clear IH.

        repeat split.
        * (* PS.Empty (PS.inter st al) *)
          intros x HH. PS_split.
          match goal with H:_ \/ x ∈ w |- _ =>
                          destruct H as [[HH1 HH2]|HH]; [|contradiction] end.
          subst w. PS_split. PS_negate.
          repeat match goal with H: _ \/ _ |- _ =>
                                 destruct H; PS_split; PS_negate;
                                   try contradiction;
                                   try (now eapply H1A; eapply PS.inter_spec; eauto);
                                   try (now eapply H2A; eapply PS.inter_spec; eauto)
                 end.
        * (* forall x, x ∈ req -> x ∈ always \/ x ∈ req' *)
          intros x Hin; rewrite PS.union_spec.
          destruct (PSP.In_dec x (((al1 ∪ w1) ∩ al2 ∪ w2) ∪ w)) as [HH|HH]; auto.
          PS_split; PS_negate.
          repeat match goal with
                   H: _ \/ _ |- _ => destruct H
                 | H:~(_ \/ _) |- _ => apply Decidable.not_or in H as (HH1 & HH2)
                 end;
            match goal with
            | H:~(x ∈ w) |- _ => assert (Hnw := H);
                                     rewrite Heqw, PS_not_union in H;
                                     destruct H as (HnxA & HnxB);
                                     apply PS_not_diff in HnxA as [HnxA | HnxA];
                                     apply PS_not_diff in HnxB as [HnxB | HnxB];
                                     try (apply PS_not_inter in HnxA as [HnxA|];
                                          [|contradiction]);
                                     try (apply PS_not_inter in HnxB as [HnxB|];
                                          [|contradiction])
            end;
            repeat match goal with
                   | H:~x ∈ w1 |- _ =>
                     rewrite Hw1 in H; PS_negate; destruct H as [H|]; now tauto
                   | H:~x ∈ w2 |- _ =>
                     rewrite Hw2 in H; PS_negate; destruct H as [H|]; now tauto
                   | H:x ∈ (PS.inter (PS.inter _ _) _) |- _ =>
                     repeat rewrite PS.inter_spec in H;
                       destruct H as ((HB1 & HB2) & HB3)
                   end.
        * (* forall x, x ∈ (PS.union stimes always) -> Can_write_in_var x s *)
          intros x Hin.
          cut (x ∈ ((st1 ∪ al1) ∪ (st2 ∪ al2))).
          destruct E as [|[[]|[]]]; subst; rewrite PS.union_spec; destruct 1 as [HH|HH]; auto with obcinv.
          PS_split; repeat match goal with H: _ \/ _ |- _ => destruct H
                                      | H: _ /\ _ |- _ => destruct H
                                      | H:PS.In _ w1 |- _ => apply Hw1 in H
                                      | H:PS.In _ w2 |- _ => apply Hw2 in H end;
          auto; subst w; PS_split; tauto.
        * (* No_Naked_Vars t *)
          apply No_Naked_Vars_add_writes.
          repeat constructor; simpl; now apply No_Naked_Vars_add_writes.

      (* switch *)
      + pose proof Hadd; apply add_defaults_switch_inv1 in Hadd as (?&?); eauto.
        * repeat split; auto.
          -- eapply add_defaults_switch_empty_stimes_always; eauto.
          -- eapply add_defaults_switch_subset_required; eauto.
        * apply Forall_forall; intros * Hin; eapply Forall_forall in IH; eauto.
          intros * Hadd'; apply IH in Hadd'; intuition.

    - (* * Comp s1 s2 *)
      simpl in Hadd.
      set (defs2 := add_defaults_stmt tyenv rq s2).
      assert (add_defaults_stmt tyenv rq s2 = defs2) as Hdefs2 by now subst defs2.
      rewrite Hdefs2 in Hadd.
      destruct defs2 as [[[t2 req2] stimes2] always2].

      set (defs1 := add_defaults_stmt tyenv req2 s1).
      assert (add_defaults_stmt tyenv req2 s1 = defs1) as Hdefs1 by now subst defs1.
      rewrite Hdefs1 in Hadd.
      destruct defs1 as [[[t1 req1] stimes1] always1].

      injection Hadd; clear Hadd; intros; subst al st rq' t.
      apply IHs1 in Hdefs1 as (H1A & H1B & H1C & H1E); clear IHs1.
      apply IHs2 in Hdefs2 as (H2A & H2B & H2C & H2E); clear IHs2.
      repeat split; auto with obcinv.
      + intro x. PS_split.
        destruct 1 as [[[? ?]|[? ?]] [?|?]]; try contradiction.
        now eapply H1A, PS.inter_spec; eauto.
        now eapply H2A, PS.inter_spec; eauto.
      + intros x HH; rewrite PS.union_spec.
        apply H2B, PS.union_spec in HH as [HH|HH]; [now intuition|].
        apply H1B, PS.union_spec in HH; intuition.
      + repeat setoid_rewrite PS.union_spec. setoid_rewrite PS.diff_spec.
        intros x [[[Hin ?]|[Hin ?]]|[Hin|Hin]]; intuition.

    - (* * Call ys clsid o f es *)
      simpl in Hadd.
      rewrite (surjective_pairing (fold_right _ _ _)) in Hadd.
      inv Hadd. repeat split; auto with obcinv.
      + intros x Hin; rewrite PS.union_spec.
        destruct (In_dec ident_eq_dec x ys) as [Hys|Hnys]; [left|right].
        * now apply ps_of_list_In; auto.
        * apply In_snd_fold_right_add_valid, ps_removes_spec; auto.
      + setoid_rewrite PS.union_spec.
        intros x [Hin|Hin]; try not_In_empty.
        apply ps_of_list_In in Hin; auto with obcinv.
      + constructor. rewrite add_valid_add_valid', app_nil_r.
        rewrite Forall_map; auto. apply Forall_forall.
        intros e Hin y ty. destruct e; try discriminate.

    - (* ExternCall *)
      inv Hadd.
      repeat split; auto with obcinv.
      + intros ? Hin. rewrite PS.union_spec.
        edestruct (equiv_dec y) as [He|Hne]; eauto using PSF.remove_2.
        now rewrite He, PS.singleton_spec; auto.
      + setoid_rewrite PS.union_spec.
        intros ? [Hin|Hin]; try not_In_empty.
        apply PSF.singleton_iff in Hin; subst; auto with obcinv.

    - (* * Skip *)
      inv Hadd; setoid_rewrite PSF.empty_iff; intuition.
  Qed.

  Corollary add_defaults_switch_inv1':
    forall tyenv req1 req2 ss d e t req' stimes always,
      add_defaults_switch tyenv (add_defaults_stmt tyenv req1) req2 e ss d = (t, req', stimes, always) ->
       PS.For_all (fun x => Can_write_in_var x (Switch e ss d)) (stimes ∪ always)
      /\ No_Naked_Vars t.
  Proof.
    intros; eapply add_defaults_switch_inv1; eauto.
    apply Forall_forall; intros ?? * Hadd.
    apply add_defaults_stmt_inv1 in Hadd; intuition.
  Qed.

  Lemma Can_write_in_add_defaults_stmt:
    forall tyenv s req t req' st al,
      add_defaults_stmt tyenv req s = (t, req', st, al) ->
      (forall x, Can_write_in_var x s <-> Can_write_in_var x t).
  Proof.
    induction s as [| |??? IH| |ys clsid o f es| |] using stmt_ind2.
    - (* Assign i e *)
      now inversion_clear 1.

    - (* AssignSt i e *)
      now inversion_clear 1.

    - (* Switch e ss *)
      intros * Hadd.
      apply add_defaults_stmt_switch_spec in Hadd as [(s1 & s2 & E & Hadd)|Hadd].
      + (* if-then-else's *)
        simpl; intro x.
        unfold add_defaults_ite in Hadd.
        destruct (add_defaults_stmt tyenv ∅ s1) as [[[t1 rq1] st1] al1] eqn: Hdefs1,
                 (add_defaults_stmt tyenv ∅ s2) as [[[t2 rq2] st2] al2] eqn: Hdefs2.

        remember ((al2 ∩ req) \ (al1 ∩ req)) as w1.
        remember ((al1 ∩ req) \ (al2 ∩ req)) as w2.
        remember (((st1 ∩ req) \ w1) ∪ ((st2 ∩ req) \ w2)) as w.
        inversion_clear Hadd.
        assert ((forall x, Can_write_in_var x s1 <-> Can_write_in_var x t1)
                /\ forall x, Can_write_in_var x s2 <-> Can_write_in_var x t2) as (IHs1 & IHs2)
          by (destruct E as [|[[]|[]]]; subst;
              repeat take (Forall _ _) and inv it; simpl in *; eauto).

        split; intro Hcan.
        * apply Can_write_in_add_writes_mono.
          inversion_clear Hcan; take (Exists _ _) and rename it into Hcan.
          constructor.
          destruct E as [|[[]|[]]]; subst; repeat (take (Exists _ _) and inv it);
            simpl in *;
            try match goal with
            | H : Can_write_in_var x s1 |- _ => left; simpl;
                                            now apply Can_write_in_add_writes_mono, IHs1
            | H : Can_write_in_var x s2 |- _ => right; left; simpl;
                                            now apply Can_write_in_add_writes_mono, IHs2
            end.
        * apply add_defaults_stmt_inv1 in Hdefs1 as (?&?& Hcw1 &?);
            apply add_defaults_stmt_inv1 in Hdefs2 as (?&?& Hcw2 &?).
          unfold PS.For_all in *.
          apply Can_write_in_add_writes in Hcan as [Hcw|Hcw].
          -- subst.
             assert (Can_write_in_var x s1 \/ Can_write_in_var x s2) as [|] by (PS_split; intuition).
             ++ destruct E as [|[[]|[]]]; subst; constructor; left; auto.
             ++ destruct E as [|[[]|[]]]; subst; constructor; right; left; auto.
          -- inversion_clear Hcw.
             repeat (take (Exists _ _) and inv it).
             ++ take (Can_write_in_var _ _) and apply Can_write_in_add_writes in it as [Hcw|Hcw].
                ** PS_split; destruct E as [|[[]|[]]]; subst; constructor; right; left; auto.
                ** destruct E as [|[[]|[]]]; subst; constructor; left; simpl; apply IHs1; auto.
             ++ take (Can_write_in_var _ _) and apply Can_write_in_add_writes in it as [Hcw|Hcw].
                ** PS_split; destruct E as [|[[]|[]]]; subst; constructor; left; auto.
                ** destruct E as [|[[]|[]]]; subst; constructor; right; left; simpl; apply IHs2; auto.

      + (* switch *)
        eapply Can_write_in_add_defaults_switch; eauto.
        * apply Forall_forall; intros * Hin; eapply Forall_forall in IH; eauto.
        * edestruct add_defaults_switch_inv1' as (Hcw &?); eauto.
          intros; setoid_rewrite Can_write_in_var_Switch in Hcw; auto.

    - (* * Comp s1 s2 *)
      simpl; intros * Hadd x.

      set (defs2 := add_defaults_stmt tyenv req s2).
      assert (add_defaults_stmt tyenv req s2 = defs2) as Hdefs2 by now subst defs2.
      rewrite Hdefs2 in Hadd.
      destruct defs2 as [[[t2 req2] stimes2] always2].

      set (defs1 := add_defaults_stmt tyenv req2 s1).
      assert (add_defaults_stmt tyenv req2 s1 = defs1) as Hdefs1 by now subst defs1.
      rewrite Hdefs1 in Hadd.
      destruct defs1 as [[[t1 req1] stimes1] always1].

      injection Hadd; clear Hadd; intros; subst al st req' t.
      specialize (IHs1 _ _ _ _ _ Hdefs1 x).
      specialize (IHs2 _ _ _ _ _ Hdefs2 x).
      split; inversion_clear 1.
      + rewrite IHs1 in *; auto with obcinv.
      + rewrite IHs2 in *; auto with obcinv.
      + rewrite <-IHs1 in *; auto with obcinv.
      + rewrite <-IHs2 in *; auto with obcinv.

    - (* * Call ys clsid o f es *)
      simpl; intros * Hadd x.
      rewrite (surjective_pairing (fold_right _ _ _)) in Hadd.
      inv Hadd. split; inversion_clear 1; auto with obcinv.

    - (* ExternCall *)
      now inversion_clear 1.

    - (* * Skip *)
      now inversion_clear 1.
  Qed.

  Lemma add_defaults_stmt_no_write:
    forall p tyenv s t me me' ve ve' req req' stimes always,
      add_defaults_stmt tyenv req s = (t, req', stimes, always) ->
      stmt_eval p me ve s (me', ve') ->
      forall x, ~ x ∈ (stimes ∪ always) ->
           Env.find x ve' = Env.find x ve.
  Proof.
    induction s as [| |??? IH | |ys clsid o f es|x |] using stmt_ind2;
      intros t me me' ve ve' rq rq' st al Hadd Heval y Hnin.

    - (* * Assign i e *)
      inv Hadd. inv Heval. rewrite Env.gso; intuition.

    - (* * AssignSt i e *)
      inv Hadd. now inv Heval.

    - (* * Switch e ss *)
      apply add_defaults_stmt_switch_spec in Hadd as [(s1 & s2 & E & Hadd)|Hadd].
      (* if-then-else's *)
      + unfold add_defaults_ite in Hadd.

        destruct (add_defaults_stmt tyenv ∅ s1) as [[[t1 rq1] st1] al1] eqn: Hdefs1,
                 (add_defaults_stmt tyenv ∅ s2) as [[[t2 rq2] st2] al2] eqn: Hdefs2.

        inv Hadd. inv Heval.
        take (nth_error _ _ = Some _) and rename it into Hin; apply nth_error_In in Hin.
        eapply Forall_forall in IH; eauto.
        destruct E as [|[[]|[]]]; subst;
          repeat (take (In _ _) and inv it); eapply IH; eauto;
            PS_split; intuition.

      (* switch *)
      + eapply add_defaults_switch_no_write in Hadd; eauto.
        eapply Forall_impl; eauto; simpl; intros; eauto.

    - (* * Comp s1 s2 *)
      inversion Hadd as [Hadd']; clear Hadd.

      set (defs2 := add_defaults_stmt tyenv rq s2).
      assert (add_defaults_stmt tyenv rq s2 = defs2) as Hdefs2 by now subst defs2.
      rewrite Hdefs2 in Hadd'.
      destruct defs2 as [[[t2 rq2] st2] al2].

      set (defs1 := add_defaults_stmt tyenv rq2 s1).
      assert (add_defaults_stmt tyenv rq2 s1 = defs1) as Hdefs1 by now subst defs1.
      rewrite Hdefs1 in Hadd'.
      destruct defs1 as [[[t1 rq1] st1] al1].

      inv Hadd'. inv Heval.
      match goal with H:stmt_eval _ _ _ s2 _ |- _ =>
        eapply IHs2 with (1:=Hdefs2) (x:=y) in H; [rewrite H|] end.
      match goal with H:stmt_eval _ _ _ s1 _ |- _ =>
        apply IHs1 with (1:=Hdefs1) (x:=y) in H; [now rewrite H|] end.
      + intro Hin; apply Hnin; clear Hnin.
        destruct (PSP.In_dec y al2). now intuition.
        apply PS.union_spec in Hin as [Hin|Hin]; intuition.
      + intro Hin; apply Hnin; clear Hnin.
        destruct (PSP.In_dec y al1). now intuition.
        apply PS.union_spec in Hin as [Hin|Hin]; intuition.

    - (* * Call ys clsid o f es *)
      simpl in Hadd.
      rewrite (surjective_pairing (fold_right _ _ _)) in Hadd.
      inv Hadd. inv Heval.
      apply Env.find_In_gsso_opt.
      intro Hin; apply Hnin. apply PSF.union_3, ps_of_list_In; auto.

    - (* ExternCall *)
      inv Hadd. inv Heval. rewrite Env.gso; intuition.

    - (* * Skip *)
      now inv Heval.
  Qed.

  (* NB: The following lemma is not true in general:

            forall tyenv s req t req' st al,
              No_Overwrites s ->
              add_defaults_stmt tyenv req s = (t, req', st, al) ->
              No_Overwrites t

         Because adding defaults to an Ifte may well introduce overwriting:

            w1 = (al2 ∩ req) \ (al1 ∩ req)
            w2 = (al1 ∩ req) \ (al2 ∩ req)
            w = ((st1 ∩ req) \ w1) ∪ (st2 ∩ req) \ w2
            ============================
            No_Overwrites
              (add_writes tyenv w
                (Ifte e (add_writes tyenv w1 t1) (add_writes tyenv w2 t2)))

         The writes of w are variables that are sometimes written by t1 or t2.
         Nothing prevents t1 from sometimes writing variables in w1.
         Nothing prevents t2 from sometimes writing variables in w2. *)

  Lemma wt_exp_add_defaults:
    forall p mems vars e,
      wt_exp p mems vars e ->
      wt_exp (add_defaults p) mems vars e.
  Proof.
    induction 1; eauto using wt_exp.
  Qed.

  Lemma wt_stmt_add_defaults:
    forall p insts mems vars s,
      wt_stmt p insts mems vars s ->
      wt_stmt (add_defaults p) insts mems vars s.
  Proof.
    induction s using stmt_ind2'; inversion_clear 1; eauto using wt_exp_add_defaults, wt_stmt.
    - econstructor; eauto using wt_exp_add_defaults.
      intros; take (Forall _ _) and eapply Forall_forall in it; eauto; simpl in *; auto.
    - match goal with H:find_class _ _ = Some _ |- _ =>
                    apply find_class_add_defaults_class in H end.
      match goal with H:find_method _ _ = Some _ |- _ =>
                      apply find_method_add_defaults_method in H;
                        rewrite find_method_map_add_defaults_method in H end.
      econstructor; eauto.
      + now rewrite add_defaults_method_m_out.
      + now rewrite add_defaults_method_m_in.
      + apply Forall_forall; intros; take (Forall _ _) and eapply Forall_forall in it;
          eauto using wt_exp_add_defaults.
    - econstructor; simpl_Forall; eauto using wt_exp_add_defaults.
  Qed.

  Corollary wt_method_add_defaults:
    forall p insts mem m,
      wt_method p insts mem m ->
      wt_method (add_defaults p) insts mem m.
  Proof.
    unfold wt_method, meth_vars. intros * (?&?).
    split; auto.
    now apply wt_stmt_add_defaults.
  Qed.

  Section AddDefaultsStmt.

    Variables (p : program)
              (insts : list (ident * ident))
              (mems  : list (ident * type))
              (vars  : list (ident * type))
              (tyenv : ident -> option type).

    Hypothesis wf_vars_tyenv:
      (forall x ty, In (x, ty) vars <-> tyenv x = Some ty).

    Hypothesis vars_enum:
      forall x ty, In (x, ty) vars -> wt_type (types p) ty.

    Lemma add_defaults_stmt_wt:
      forall s t req req' stimes always,
        add_defaults_stmt tyenv req s = (t, req', stimes, always) ->
        wt_stmt p insts mems vars s ->
        wt_stmt p insts mems vars t
        /\ PS.For_all (fun x => InMembers x vars) stimes
        /\ PS.For_all (fun x => InMembers x vars) always
        /\ PS.For_all (fun x => x ∈ req \/ InMembers x vars) req'.
    Proof.
      induction s as [| |??? IHd IH| |ys clsid o f es|x|] using stmt_ind2';
      intros * Hadd WTs;
        try (injection Hadd; intros; subst always stimes req' t).

      - (* * Assign i e *)
        repeat split; auto using PS_For_all_empty; intros ? Hin.
        + apply PS.singleton_spec in Hin; subst.
          inv WTs. eauto using In_InMembers.
        + apply PS.remove_spec in Hin as (? & ?); auto.

      - (* * AssignSt i e *)
        repeat split; auto using PS_For_all_empty; intros ??; auto.

      - (* * Switch e ss *)
        apply add_defaults_stmt_switch_spec in Hadd as [(s1 & s2 & E & Hadd)|Hadd].
        + (* * Ifte e s1 s2 *)
          inversion_clear WTs as [| |???????? Hwtd Hwtss| | | |].
          unfold add_defaults_ite in Hadd.
          simpl in Hadd.
          destruct (add_defaults_stmt tyenv ∅ s1) as [[[t1 rq1] st1] al1] eqn: Hdefs1.
          destruct (add_defaults_stmt tyenv ∅ s2) as [[[t2 rq2] st2] al2] eqn: Hdefs2.
          inv Hadd.
          assert (wt_stmt p insts mems vars s1
                  /\ wt_stmt p insts mems vars s2) as (Hwts1 & Hwts2).
          { destruct E as [|[[]|[]]]; split; subst; auto;
              take (forall s, In _ _ -> wt_stmt _ _ _ _ _) and apply it; auto with datatypes. }

          assert (wt_stmt p insts mems vars t1
                  /\ PS.For_all (fun x => InMembers x vars) st1
                  /\ PS.For_all (fun x => InMembers x vars) al1
                  /\ PS.For_all (fun x => x ∈ ∅ \/ InMembers x vars) rq1
                  /\ wt_stmt p insts mems vars t2
                  /\ PS.For_all (fun x => InMembers x vars) st2
                  /\ PS.For_all (fun x => InMembers x vars) al2
                  /\ PS.For_all (fun x => x ∈ ∅ \/ InMembers x vars) rq2)
            as (WTt1 & Hst1 & Hal1 & Hrq1 & WTt2 & Hst2 & Hal2 & Hrq2)
              by (destruct E as [|[[]|[]]]; subst;
                    inversion_clear IH as [|?? IH1 IH']; inversion_clear IH' as [|?? IH2];
                    simpl in *; try apply IH1 in Hdefs1; try apply IH2 in Hdefs2;
                    try apply IHd in Hdefs1; try apply IHd in Hdefs2; auto; intuition).

          repeat split.
          * setoid_rewrite wf_vars_tyenv' in Hst1;
            setoid_rewrite wf_vars_tyenv' in Hst2;
            setoid_rewrite wf_vars_tyenv' in Hal1;
            setoid_rewrite wf_vars_tyenv' in Hal2; eauto.
            rewrite <-add_writes_wt;
              auto using PS_For_all_union, PS_For_all_diff, PS_For_all_inter.
            econstructor; try rewrite <-add_writes_wt;
              eauto using PS_For_all_union, PS_For_all_diff, PS_For_all_inter.
            -- destruct E as [|[[]|[]]]; subst; simpl in *; auto.
            -- intros. repeat take (In (Some _) _) and inv it; try discriminate.
               take (Some _ = Some _) and inv it.
               rewrite <-add_writes_wt;
                 eauto using PS_For_all_union, PS_For_all_diff, PS_For_all_inter.
          * intros x HH. PS_split.
            repeat match goal with H:_ \/ _ |- _ => destruct H; PS_split end;
              match goal with
              | Hi:PS.In ?x ?S, Hf:PS.For_all _ ?S |- InMembers ?x _ =>
                now apply PS_In_Forall with (1:=Hf); auto end.
          * intros x HH. PS_split.
            repeat match goal with H:_ \/ _ |- _ => destruct H; PS_split end;
              match goal with
              | Hi:PS.In ?x ?S, Hf:PS.For_all _ ?S |- InMembers ?x _ =>
                now apply PS_In_Forall with (1:=Hf); auto end.
          * intros x HH. PS_split.
            repeat match goal with
                   | H:_ \/ _ |- _ => destruct H; PS_split
                   | Hi:PS.In ?x ?S, Hf:PS.For_all _ ?S |- _ =>
                     apply PS_In_Forall with (1:=Hf) in Hi as [?|?]
                   | H:PS.In _ ∅ |- _ =>
                     now apply not_In_empty in H
                   end; auto; contradiction.

        + (* switch *)
          eapply add_defaults_switch_wt in Hadd; eauto.
          * apply Forall_forall; intros os Hin; eapply Forall_forall in IH; eauto.
            destruct os; simpl in *; auto.
            intros; edestruct IH as (?&?&?& Hreq'); eauto.
            repeat split; auto.
            intros ? Hin'; apply Hreq' in Hin' as [|]; auto.
            PS_split; contradiction.
          * intros; edestruct IHd as (?&?&?& Hreq'); eauto.
            repeat split; auto.
            intros ? Hin'; apply Hreq' in Hin' as [|]; auto.
            PS_split; contradiction.

      - (* * Comp s1 s2 *)
        inversion_clear WTs as [| | |? ? Hwt1 Hwt2| | |].
        simpl in Hadd.
        set (defs2 := add_defaults_stmt tyenv req s2).
        assert (add_defaults_stmt tyenv req s2 = defs2) as Hdefs2 by now subst defs2.
        rewrite Hdefs2 in Hadd.
        destruct defs2 as [[[t2 rq2] stimes2] always2].

        set (defs1 := add_defaults_stmt tyenv rq2 s1).
        assert (add_defaults_stmt tyenv rq2 s1 = defs1) as Hdefs1 by now subst defs1.
        rewrite Hdefs1 in Hadd.
        destruct defs1 as [[[t1 rq1] stimes1] always1].

        injection Hadd; clear Hadd; intros; subst always stimes req' t.
        apply IHs1 with (2:=Hwt1) in Hdefs1 as (IHt1 & Hst1 & Hal1 & Hrq1).
        apply IHs2 with (2:=Hwt2) in Hdefs2 as (IHt2 & Hst2 & Hal2 & Hrq2).
        repeat split; eauto using wt_stmt,
                      PS_For_all_union, PS_For_all_diff, PS_For_all_diff.
        intros x Hin.
        apply PS_In_Forall with (1:=Hrq1) in Hin as [Hin|Hin]; auto.

      - (* * Call ys clsid o f es *)
        simpl in Hadd.
        rewrite (surjective_pairing (fold_right _ _ _)) in Hadd.
        inv Hadd. repeat split; auto using PS_For_all_empty; inv WTs.
        + econstructor; eauto; rewrite add_valid_add_valid', app_nil_r.
          * apply Forall2_map_1.
            match goal with H:Forall2 _ _ _ |- _ =>
                            apply Forall2_impl_In with (2:=H) end.
            intros e (x, ty) Hin1 Hin2 Htye; rewrite <-Htye. now destruct e.
          * apply Forall_map.
            match goal with H:Forall _ _ |- _ =>
                            apply Forall_impl_In with (2:=H) end.
            intros e Hin WTe. destruct e; simpl; inv WTe; eauto using wt_exp.
        + intros x Hin. apply ps_of_list_In in Hin.
          match goal with H:Forall2 _ _ _ |- _ =>
            apply Forall2_in_left with (1:=H) in Hin as (xty & Hin1 & Hin2) end.
          eauto using In_InMembers.
        + unfold PS.For_all.
          match goal with H:Forall (wt_exp _ _ _) ?xs |- _ =>
            revert H; clear; induction xs as [|e ? IH] end; simpl; intros WT x Hin.
          now apply ps_removes_spec in Hin as (? & ?); auto.
          apply Forall_cons2 in WT as (WTe & WTes).
          destruct e; auto. simpl in Hin.
          inversion_clear WTe.
          apply PS.add_spec in Hin as [Hin|Hin]; subst; eauto using In_InMembers.

      - (* ExternalCall *)
        repeat split; auto using PS_For_all_empty; intros ? Hin.
        + apply PS.singleton_spec in Hin; subst.
          inv WTs. eauto using In_InMembers.
        + apply PS.remove_spec in Hin as (? & ?); auto.

      - (* * Skip *)
        repeat split; auto using PS_For_all_empty; intros x Hin; auto.
    Qed.

    Corollary add_defaults_switch_wt':
      forall e ss d t req req' stimes always,
        add_defaults_switch tyenv (add_defaults_stmt tyenv ∅) req e ss d = (t, req', stimes, always) ->
        wt_stmt p insts mems vars (Switch e ss d) ->
        wt_stmt p insts mems vars t
        /\ PS.For_all (fun x => InMembers x vars) stimes
        /\ PS.For_all (fun x => InMembers x vars) always
        /\ PS.For_all (fun x => x ∈ req \/ InMembers x vars) req'.
    Proof.
      intros * Hadd WT.
      eapply add_defaults_switch_wt with (5 := Hadd); eauto.
      - apply Forall_forall; intros os ?.
        destruct os; simpl; auto.
        intros * Hadd' WT'.
        apply add_defaults_stmt_wt in Hadd' as (?&?&?& Hreq); auto.
        intuition.
        intros ? Hin; apply Hreq in Hin as []; auto.
        PS_split; contradiction.
      - intros * Hadd' WT'.
        apply add_defaults_stmt_wt in Hadd' as (?&?&?& Hreq); auto.
        intuition.
        intros ? Hin; apply Hreq in Hin as []; auto.
        PS_split; contradiction.
    Qed.

    (* Having [wt_stmt] ensures that the number of variables to the left of a
       function call matches the number of function outputs, and allows us to
       conclude that all those variables are written to. *)

    Lemma add_defaults_stmt_inv2:
      forall s t me me' ve ve' req req' stimes always,
        (forall ome ome' clsid f vos rvos,
            Forall (fun vo => vo <> None) vos ->
            stmt_call_eval p ome clsid f vos ome' rvos ->
            Forall (fun x => x <> None) rvos) ->
        add_defaults_stmt tyenv req s = (t, req', stimes, always) ->
        stmt_eval p me ve t (me', ve') ->
        wt_stmt p insts mems vars s ->
        PS.For_all (fun x => Env.In x ve) req' ->
        (forall x, ~x ∈ (stimes ∪ always) -> Env.find x ve' = Env.find x ve)
        /\ PS.For_all (fun x => Env.In x ve') always.
    Proof.
      intros * Hcall Hadd Heval Hwt Hre1.
      revert t me me' ve ve' Heval req req' stimes always Hadd Hre1.
      induction s as [| |??? IH| |ys clsid o f es|x|] using stmt_ind2;
        intros t me me' ve ve' Heval rq rq' st al Hadd Hre1.

      - (* * Assign i e *)
        inv Hadd. inv Heval.
        repeat split; auto using PSP.empty_inter_1.
        + intros ? Hnin. rewrite Env.gso; auto.
          intro; now apply Hnin, PSF.union_3, PS.singleton_spec.
        + intros ? Hin. apply PSP.FM.singleton_1 in Hin.
          apply Env.Props.P.F.add_in_iff; auto.

      - (* * AssignSt i e *)
        inv Hadd. inv Heval.
        setoid_rewrite PSF.empty_iff; intuition.
        apply PS_For_all_empty.

      - (* * Switch e ss *)
        apply add_defaults_stmt_switch_spec in Hadd as [(s1 & s2 & E & Hadd)|Hadd].
        + (* if-then-else's *)
          unfold add_defaults_ite in Hadd.
          destruct (add_defaults_stmt tyenv ∅ s1) as [[[t1 rq1] st1] al1] eqn: Hdefs1.
          destruct (add_defaults_stmt tyenv ∅ s2) as [[[t2 rq2] st2] al2] eqn: Hdefs2.
          inv Hadd.

          (* use typing to deduce that added writes are in tyenv *)
          inversion_clear Hwt as [| |???????? Hwtd Hwtss| | | |].
          assert (wt_stmt p insts mems vars s1
                  /\ wt_stmt p insts mems vars s2) as (Hwt1 & Hwt2).
          { destruct E as [|[[]|[]]]; split; subst; auto;
              take (forall s, In _ _ -> wt_stmt _ _ _ _ _) and apply it; auto with datatypes. }
          match goal with
            H: Forall ?P ss |- _ => assert (P (Some s1) /\ P (Some s2)) as (IHs1 & IHs2)
                by (destruct E as [|[[]|[]]]; subst; split;
                    inversion_clear H as [|??? H']; inversion_clear H'; eauto)
          end.
          specialize (IHs1 Hwt1); specialize (IHs2 Hwt2).

          pose proof (add_defaults_stmt_wt _ _ _ _ _ _ Hdefs1 Hwt1)
            as (Ht1 & HTst1 & HTal1 & HTreq1).
          pose proof (add_defaults_stmt_wt _ _ _ _ _ _ Hdefs2 Hwt2)
            as (Ht2 & HTst2 & HTal2 & HTreq2).
          clear Ht1 Ht2 Hwt1 Hwt2.
          setoid_rewrite wf_vars_tyenv' in HTst1;
            setoid_rewrite wf_vars_tyenv' in HTal1;
            setoid_rewrite wf_vars_tyenv' in HTst2;
            setoid_rewrite wf_vars_tyenv' in HTal2; eauto.

          apply stmt_eval_add_writes_split in Heval as (meW & veW & HevalW & Heval).

          (* massage the stmt_evals *)
          inversion_clear Heval as [| | | | |? ? ? ? ? ? ? ? ? ? ? ? Heval'|].
          assert (exists meW' veW',
                     stmt_eval p meW veW
                               (if s0
                                then add_writes tyenv ((al2 ∩ rq) \ (al1 ∩ rq)) Skip
                                else add_writes tyenv ((al1 ∩ rq) \ (al2 ∩ rq)) Skip)
                               (meW', veW')
                     /\ stmt_eval p meW' veW' (if s0 then t1 else t2) (me', ve'))
            as (meW' & veW' & HevalW' & Heval)
              by (take (nth_error _ _ = _) and rename it into Hin; apply nth_error_In in Hin;
                  repeat (take (In s0 _) and inv it); simpl;
                  apply stmt_eval_add_writes_split in Heval' as (?&?&?&?); eauto).
          clear Heval'.

          (* factor out obligations for inductive hypotheses *)
          assert (forall x, (x ∈ rq1 \/ x ∈ rq2) -> Env.In x veW') as Hreq'.
          { intros x Hrq1.
            apply stmt_eval_mono with (x:=x) in HevalW'; auto; clear HevalW'.
            match goal with H:stmt_eval _ _ _ (add_writes _ ?W Skip) _ |- _ =>
                            destruct (PSP.In_dec x W) as [Hw|Hnw] end.
            - apply stmt_eval_add_writes in HevalW; auto.
              apply PS_For_all_union;
                auto using PS_For_all_diff, PS_For_all_inter.
            - apply stmt_eval_mono with (x:=x) in HevalW; auto.
              intuition.
          }
          assert (forall x, x ∈ rq1 -> Env.In x veW') as Hreq1 by auto.
          assert (forall x, x ∈ rq2 -> Env.In x veW') as Hreq2 by auto.
          clear Hreq'.

          (* Put some structure back into the sets *)
          remember ((al2 ∩ rq) \ (al1 ∩ rq)) as w1.
          remember ((al1 ∩ rq) \ (al2 ∩ rq)) as w2.
          remember (((st1 ∩ rq) \ w1) ∪ ((st2 ∩ rq) \ w2)) as w.
          setoid_rewrite (simplify_write_sets w w1 w2 _ _ _ _ _ Heqw1 Heqw2 Heqw).
          split.
          * (* forall x, ~x ∈ (st ∪ al) -> Env.find x env' = Env.find x env *)
            intros x HH.
            repeat rewrite PS_not_union in HH.
            destruct HH as (Hnw & Hnw1 & Hnw2 & Hnal1 & Hnal2 & Hnst1 & Hnst2).
            destruct s0; simpl in *.
            -- clear IHs2; specialize (IHs1 _ _ _ _ _ Heval _ _ _ _ Hdefs1 Hreq1).
               destruct IHs1 as (IH1 & IH2).
               rewrite IH1; [|now apply PS_not_union; auto].
               rewrite stmt_eval_add_writes_Skip_other with (1:=HevalW'); auto.
               rewrite stmt_eval_add_writes_Skip_other with (1:=HevalW); auto.
            -- clear IHs1; specialize (IHs2 _ _ _ _ _ Heval _ _ _ _ Hdefs2 Hreq2).
               destruct IHs2 as (IH1 & IH2).
               rewrite IH1; [|now apply PS_not_union; auto].
               rewrite stmt_eval_add_writes_Skip_other with (1:=HevalW'); auto.
               rewrite stmt_eval_add_writes_Skip_other with (1:=HevalW); auto.
          * (* forall x, x ∈ al -> Env.In x env' *)
            unfold PS.For_all.
            setoid_rewrite PS.union_spec.
            setoid_rewrite PS.inter_spec.
            setoid_rewrite PS.union_spec.
            pose proof (add_defaults_stmt_inv1 _ _ _ _ _ _ _ Hdefs1) as (H1A & H1B & H1C & H1E).
            pose proof (add_defaults_stmt_inv1 _ _ _ _ _ _ _ Hdefs2) as (H2A & H2B & H2C & H2E).
            intros x [[[Hal1|Hiw1] [Hal2|Hiw2]]|Hiw].
            -- destruct s0.
               ++ now apply IHs1 with (2:=Hdefs1) (3:=Hreq1) in Heval as (? & ?); auto.
               ++ now apply IHs2 with (2:=Hdefs2) (3:=Hreq2) in Heval as (? & ?); auto.
            -- destruct s0.
               ++ now apply IHs1 with (2:=Hdefs1) (3:=Hreq1) in Heval as (? & ?); auto.
               ++ apply stmt_eval_mono with (x:=x) in Heval; auto.
                  apply stmt_eval_add_writes in HevalW'; auto.
                  subst; auto using PS_For_all_diff, PS_For_all_inter.
            -- destruct s0.
               ++ apply stmt_eval_mono with (x:=x) in Heval; auto.
                  apply stmt_eval_add_writes in HevalW'; auto.
                  subst; auto using PS_For_all_diff, PS_For_all_inter.
               ++ now apply IHs2 with (2:=Hdefs2) (3:=Hreq2) in Heval as (? & ?); auto.
            -- apply stmt_eval_mono with (x:=x) in Heval; destruct s0; auto;
                 apply stmt_eval_add_writes in HevalW';
                 subst; auto using PS_For_all_diff, PS_For_all_inter.
            -- apply stmt_eval_mono with (x:=x) in Heval; [destruct s0|]; auto.
               apply stmt_eval_mono with (x:=x) in HevalW'; auto.
               apply stmt_eval_add_writes in HevalW; auto.
               subst; apply PS_For_all_union;
                 auto using PS_For_all_diff, PS_For_all_inter.

        + (* switch *)
          edestruct add_defaults_switch_wt' as (?&?&?&?); eauto.
          eapply add_defaults_switch_inv2 in Hadd; eauto.
          eapply Forall_impl; eauto; simpl; intros; eauto.

      - (* * Comp s1 s2 *)
        pose proof (add_defaults_stmt_inv1 _ _ _ _ _ _ _ Hadd) as (HIc & HId).

        inversion_clear Hwt as [| | |? ? Hwt1 Hwt2| | |].
        specialize (IHs1 Hwt1). specialize (IHs2 Hwt2).
        clear Hwt1 Hwt2. inversion Hadd as [Hadd']; clear Hadd.

        (* unfold the two recursive calls to add_defaults_stmt *)
        set (defs2 := add_defaults_stmt tyenv rq s2).
        assert (add_defaults_stmt tyenv rq s2 = defs2) as Hdefs2 by now subst defs2.
        rewrite Hdefs2 in Hadd'.
        destruct defs2 as [[[t2 rq2] st2] al2].
        pose proof (add_defaults_stmt_inv1 _ _ _ _ _ _ _ Hdefs2)
          as (HI2c & HI2d & HI2e & HI2g).

        set (defs1 := add_defaults_stmt tyenv rq2 s1).
        assert (add_defaults_stmt tyenv rq2 s1 = defs1) as Hdefs1 by now subst defs1.
        rewrite Hdefs1 in Hadd'.
        destruct defs1 as [[[t1 rq1] st1] al1].
        pose proof (add_defaults_stmt_inv1 _ _ _ _ _ _ _ Hdefs1)
          as (HI1c & HI1d & HI1e & HI1g).

        injection Hadd'; clear Hadd'; intros; subst al st rq' t.

        (* massage the stmt_evals *)
        inv Heval.
        match goal with H1:stmt_eval _ _ _ t1 _, H2:stmt_eval _ _ _ t2 _ |- _ =>
                        specialize (IHs1 _ _ _ _ _ H1 _ _ _ _ Hdefs1 Hre1);
                          rename H1 into Heval1; clear Hdefs1 end.
        destruct IHs1 as (HI1a & HI1b).

        (* factor out obligations for inductive hypotheses *)
        assert (forall x, x ∈ rq2 -> Env.In x ve1) as Hre2.
        { intros x Hin. apply HI1d, PS.union_spec in Hin.
          destruct Hin as [|Hin]; eauto using stmt_eval_mono. }
        match goal with H1:stmt_eval _ _ _ t1 _, H2:stmt_eval _ _ _ t2 _ |- _ =>
                        specialize (IHs2 _ _ _ _ _ H2 _ _ _ _ Hdefs2 Hre2);
                          rename H2 into Heval2; clear Hdefs2 end.
        destruct IHs2 as (HI2a & HI2b).

        split.
        + (* forall x, ~x ∈ (st ∪ al) -> Env.find x env' = Env.find x env *)
          intros x Hnin.
          cut (~ x ∈ ((st1 ∪ al1) ∪ (st2 ∪ al2))).
          * intros Hnin'. repeat rewrite PS_not_union in Hnin'.
            destruct Hnin' as [[HH1 HH2] [HH3 HH4]].
            rewrite HI2a, HI1a; try rewrite PS_not_union; auto.
          * repeat rewrite PS_not_union in Hnin.
            destruct Hnin as [[HH1 HH2] [HH3 HH4]].
            rewrite PS.diff_spec in HH1, HH2.
            repeat setoid_rewrite PS.union_spec.
            destruct 1 as [[HH|HH]|[HH|HH]]; auto.
        + (* forall x, x ∈ al -> Env.In x env' *)
          intros x HH. apply PS.union_spec in HH.
          destruct HH; eauto using stmt_eval_mono.

      - (* * Call ys clsid o f es *)
        simpl in Hadd.
        rewrite (surjective_pairing (fold_right _ _ _)) in Hadd.
        inv Hadd. inv Heval. split.
        + (* forall x, ~x ∈ (st ∪ al) -> Env.find x env' = Env.find x env *)
          intros x Hnin.
          apply Env.find_In_gsso_opt.
          rewrite PSP.empty_union_1, ps_of_list_In in Hnin; auto.
        + (* forall x, x ∈ al -> Env.In x env' *)
          assert (length ys = length rvos) as Hlys.
          { inv Hwt.
            match goal with Hfa:Forall2 _ ys _,
                                He:stmt_call_eval _ _ _ _ _ _ _ |- _ =>
                            apply Forall2_length in Hfa; rename Hfa into Hlen1;
                              inversion_clear He as [? ? ? ? ? ? ? ? ? ? ? ? ? ? ? Hlen2] end.
            rewrite Forall2_map_1 in Hlen2. apply Forall2_length in Hlen2.
            match goal with H1:find_class ?c ?p = Some _,
                               H2:find_class ?c ?p = Some _,
                                  H3:find_method _ _ = Some _,
                                     H4:find_method _ _ = Some _ |- _ =>
                            rename H1 into Hf1; rename H2 into Hf2;
                              rename H3 into Hm1; rename H4 into Hm2 end.
            rewrite Hf1 in Hf2; inv Hf2.
            rewrite Hm1 in Hm2; inv Hm2.
            now rewrite Hlen1, Hlen2. }

          assert (Forall2 (fun _ _ => True) ys rvos) as Hlys' by (apply Forall2_forall; auto).
          match goal with H:stmt_call_eval _ _ _ _ _ _ _ |- _ =>
                          apply Hcall in H; rename H into Hnn end.
          *{ intros x Hinadds.
             apply ps_of_list_In in Hinadds.
             revert Hnn Hinadds Hlys'; clear; intros Hnn Hinadds Hlys'.
             induction Hlys'; inv Hinadds.
             - inversion_clear Hnn as [|? ? Hrvo Hrvos].
               apply not_None_is_Some in Hrvo. destruct Hrvo as (rv & Hrvo).
               rewrite Hrvo; simpl. apply Env.Props.P.F.add_in_iff; auto.
             - inversion_clear Hnn as [|? ? Hrvo Hrvos].
               apply not_None_is_Some in Hrvo. destruct Hrvo as (rv & Hrvo).
               rewrite Hrvo.
               rewrite Env.adds_opt_cons_cons.
               rewrite Env.Props.P.F.add_in_iff; auto using IHHlys'.
           }
          * match goal with H:Forall2 (exp_eval _ _) (fst _) vos |- _ =>
              rewrite add_valid_add_valid', app_nil_r in H; rename H into Hvos end.
            rewrite Forall2_map_1 in Hvos.
            apply Forall_forall. intros vo Hin.
            apply Forall2_in_right with (2:=Hin) in Hvos as (e & Hein & He).
            destruct e; simpl; inv He; discriminate.

      - (* ExternCall *)
        inv Hadd. inv Heval.
        repeat split; auto using PSP.empty_inter_1.
        + intros ? Hnin. rewrite Env.gso; auto.
          intro; now apply Hnin, PSF.union_3, PS.singleton_spec.
        + intros ? Hin. apply PSP.FM.singleton_1 in Hin.
          apply Env.Props.P.F.add_in_iff; auto.

      - (* * Skip *)
        inv Hadd. inv Heval.
        setoid_rewrite PSF.empty_iff; intuition.
        apply PS_For_all_empty.
    Qed.

    Import Basics.

    Global Instance in1_notin2_Proper1:
      Proper (PS.Equal ==> PS.Equal ==> Env.refines eq ==> Env.refines eq --> impl)
             in1_notin2.
    Proof.
      intros S1 S2 HS12 T1 T2 HT12 ve0 ve0' Henv0 ve1 ve1' Henv1'.
      intros (HH1 & HH2); split.
      - intros x HS2. rewrite <-HS12 in HS2.
        setoid_rewrite Henv0 in HH1; auto.
      - intros x HT2. rewrite <-HT12 in HT2.
        setoid_rewrite Henv1' in HH2; auto.
    Qed.

    Global Instance in1_notin2_Proper2:
      Proper (PS.Equal ==> PS.Equal ==> eq ==> eq ==> iff) in1_notin2.
    Proof.
      intros S1 S2 HS12 T1 T2 HT12 ve0 ve0' Henv0 ve1 ve1' Henv1'; subst.
      split; intros (HH1 & HH2); split.
      - intros x HS2. rewrite <-HS12 in HS2; auto.
      - intros x HT2. rewrite <-HT12 in HT2; auto.
      - intros x HS1. rewrite HS12 in HS1; auto.
      - intros x HT1. rewrite HT12 in HT1; auto.
    Qed.

    Lemma in1_notin2_add1:
      forall ve1 ve2 x S1 S2,
        in1_notin2 (PS.add x S1) S2 ve1 ve2 ->
        in1_notin2 S1 S2 ve1 ve2 /\ Env.In x ve1.
    Proof.
      destruct 1 as (Hin1 & Hout2).
      repeat split; auto.
      now intros y Hin; apply Hin1, PS.add_spec; auto.
      now apply Hin1, PS.add_spec; auto.
    Qed.

    Lemma in1_notin2_Var_In:
      forall ve' ve es acc S,
        in1_notin2 (snd (fold_right add_valid acc es)) S ve' ve ->
        Forall (fun e => match e with Var x _ => Env.In x ve' | _ => True end) es.
    Proof.
      induction es as [|e es IH]; auto.
      intros acc S HH.
      destruct e; simpl in *; try (now apply IH in HH; auto).
      apply in1_notin2_add1 in HH as (HH & Hin).
      apply IH in HH; auto.
    Qed.

    Lemma in1_notin2_Var_Not_In:
      forall ys s1 ve' ve,
        in1_notin2 s1 (PSP.of_list ys) ve' ve ->
        Forall (fun x => ~ Env.In x ve) ys.
    Proof.
      intros * (?& Hnin).
      apply Forall_forall; intros * Hin.
      apply Hnin, ps_of_list_In; auto.
    Qed.

    Lemma add_defaults_stmt_correct:
      forall p' s req t req' st al,
        program_refines (fun _ _ => all_in1) p p' ->
        (forall ome ome' clsid f vos rvos,
            Forall (fun vo => vo <> None) vos ->
            stmt_call_eval p ome clsid f vos ome' rvos ->
            Forall (fun x => x <> None) rvos) ->
        No_Overwrites s ->
        wt_stmt p insts mems vars s ->
        add_defaults_stmt tyenv req s = (t, req', st, al) ->
        stmt_refines p p' (in1_notin2 req' (st ∪ al)) t s.
    Proof.
      intros p' s rq t rq' st al Hpr Hcall Hno Hwt Hadd
             me ve1 ve2 me' ve2' Hpre Henv Heval.
      revert t rq rq' st al Hadd ve1 Henv Hpre; revert dependent ve2; revert me ve2' me'.
      induction s as [| |??? IH| |ys clsid o f es|x|] using stmt_ind2;
        intros; inv Heval.

      - (* Assign x e *)
        inv Hadd.
        exists (Env.add x v ve1).
        eauto using Env.refines_add_both, exp_eval_refines, stmt_eval.

      - (* AssignSt x e *)
        inv Hadd; eauto using exp_eval_refines, stmt_eval.

      - (* Switch e ss *)
        apply add_defaults_stmt_switch_spec in Hadd as [(s1 & s2 & E & Hadd)|Hadd].

        (* if-then-else's *)
        + rename ve2 into ve0, ve1 into ve0', ve2' into ve3, Henv into Henv0'.
          unfold add_defaults_ite in Hadd.
          inversion_clear Hwt as [| |???????? Hwtd Hwtss| | | |].
          destruct (add_defaults_stmt tyenv ∅ s1) as [[[t1 rq1] st1] al1] eqn: Hdefs1.
          destruct (add_defaults_stmt tyenv ∅ s2) as [[[t2 rq2] st2] al2] eqn: Hdefs2.
          inv Hadd.

          take (nth_error _ _ = _) and rename it into Nth.
          pose proof Nth as Hin; apply nth_error_In in Hin.

          assert (wt_stmt p insts mems vars s1
                  /\ wt_stmt p insts mems vars s2) as (Hwt1 & Hwt2).
          { destruct E as [|[[]|[]]]; split; subst; auto;
              take (forall s, In _ _ -> wt_stmt _ _ _ _ _) and apply it; auto with datatypes. }

          assert (No_Overwrites (or_default s s0)) as NOO
            by (inversion_clear Hno as [| |? ? ? Hnoss| | | |];
                  eapply Forall_forall in Hnoss; eauto).
          assert (wt_stmt p insts mems vars (or_default s s0)) as WT
              by (destruct s0; auto).
          eapply Forall_forall in IH; eauto.
          take (stmt_eval _ _ _ _ _) and rename it into Heval.
          specialize (IH NOO WT _ _ _ _ Heval).

          pose proof (add_defaults_stmt_wt _ _ _ _ _ _ Hdefs1 Hwt1)
            as (Hwt1' & Hvst1 & Hval1 & Hreq1).
          pose proof (add_defaults_stmt_wt _ _ _ _ _ _ Hdefs2 Hwt2)
            as (Hwt2' & Hvst2 & Hval2 & Hreq2).

          remember ((al2 ∩ rq) \ (al1 ∩ rq)) as w1.
          remember ((al1 ∩ rq) \ (al2 ∩ rq)) as w2.
          remember (((st1 ∩ rq) \ w1) ∪ ((st2 ∩ rq) \ w2)) as w.
          setoid_rewrite (simplify_write_sets w w1 w2 _ _ _ _ _ Heqw1 Heqw2 Heqw) in Hpre.

          assert (PS.For_all (fun x => ~Env.In x ve0) w) as Hwenv0.
          { intros ??. apply Hpre. repeat rewrite PSF.union_iff; auto. }
          assert (PS.For_all (fun x => InMembers x vars) w) as Hwim
              by (now subst w; apply PS_For_all_union;
                  apply PS_For_all_diff, PS_For_all_inter).
          destruct (stmt_eval_add_writes_Skip tyenv p _ wf_vars_tyenv me w _ _ Henv0' Hwenv0 Hwim)
            as (ve1' & Henv1' & Heval1' & Hmono1 & Hin1').

          assert (PS.For_all (fun x => ~Env.In x ve0) w1
                  /\ PS.For_all (fun x => ~Env.In x ve0) w2) as (Hwenv1 & Hwenv2).
          { split; intros ??; apply Hpre; repeat rewrite PSF.union_iff; auto. }
          assert (PS.For_all (fun x => InMembers x vars) w1
                  /\ PS.For_all (fun x => InMembers x vars) w2) as (Hwim1 & Hwim2)
              by (subst w1 w2; split; apply PS_For_all_diff, PS_For_all_inter; auto).
          destruct (stmt_eval_add_writes_Skip tyenv p _ wf_vars_tyenv me w1 _ _ Henv1' Hwenv1 Hwim1)
            as (ve21' & Henv21' & Heval21' & Hmono21 & Hin21').
          destruct (stmt_eval_add_writes_Skip tyenv p _ wf_vars_tyenv me w2 _ _ Henv1' Hwenv2 Hwim2)
            as (ve22' & Henv22' & Heval22' & Hmono22 & Hin22').

          destruct Hpre as (Hpre1 & Hpre2).
          assert (in1_notin2 rq1 (st1 ∪ al1) ve21' ve0).
          { split.
            - intros x Hrq1.
              destruct (PSP.In_dec x w1) as [Hw1|Hnw1].
              + now apply PS_In_Forall with (1:=Hin21') (2:=Hw1).
              + apply (Hmono21 x).
                destruct (PSP.In_dec x w) as [Hw|Hnw].
                * now apply PS_In_Forall with (1:=Hin1') (2:=Hw).
                * apply (Hmono1 x); apply Hpre1. intuition.
            - intros; apply Hpre2; PS_split; tauto.
          }
          assert (in1_notin2 rq2 (st2 ∪ al2) ve22' ve0).
          { split.
            - intros x Hrq2.
              destruct (PSP.In_dec x w2) as [Hw2|Hnw2].
              + now apply PS_In_Forall with (1:=Hin22') (2:=Hw2).
              + apply (Hmono22 x).
                destruct (PSP.In_dec x w) as [Hw|Hnw].
                * now apply PS_In_Forall with (1:=Hin1') (2:=Hw).
                * apply (Hmono1 x); apply Hpre1. intuition.
            - intros; apply Hpre2; PS_split; tauto.
          }

          destruct E as [|[[]|[]]], c as [|[]]; subst; simpl in Nth;
            try (rewrite nth_error_nil in Nth; discriminate); inv Nth;
              match goal with
                | H : exp_eval _ _ _ (Some (Venum 0)) |- _ =>
                  edestruct IH with (ve1 := ve21') as (ve3' &?&?); eauto
                | H : exp_eval _ _ _ (Some (Venum 1)) |- _ =>
                  edestruct IH with (ve1 := ve22') as (ve3' &?&?); eauto
              end;
              exists ve3'; split; auto;
                apply stmt_eval_add_writes_split;
                exists me, ve1'; split; auto;
                  econstructor; eauto using exp_eval_refines; simpl; eauto;
                    simpl;
                    apply stmt_eval_add_writes_split; eauto.

        + (* switch *)
          edestruct add_defaults_switch_wt' as (?&?&?&?); eauto.
          eapply add_defauts_switch_correct in Hadd; eauto using stmt_eval.
          eapply Forall_impl; eauto; simpl; intros; eauto.
          intros ????????; eauto.

      - (* Comp s1 s2 *)
        simpl in *.
        rename ve1 into ve0', ve0 into ve1, ve2' into ve2, ve2 into ve0, Henv into Henv0.

        inversion_clear Hwt as [| | |? ? Hwt1 Hwt2| | |].

        set (defs2 := add_defaults_stmt tyenv rq s2).
        assert (add_defaults_stmt tyenv rq s2 = defs2) as Hdefs2 by now subst defs2.
        rewrite Hdefs2 in Hadd.
        destruct defs2 as [[[t2 rq2] stimes2] always2].

        set (defs1 := add_defaults_stmt tyenv rq2 s1).
        assert (add_defaults_stmt tyenv rq2 s1 = defs1) as Hdefs1 by now subst defs1.
        rewrite Hdefs1 in Hadd.
        destruct defs1 as [[[t1 rq1] stimes1] always1].
        inv Hadd.
        assert (in1_notin2 rq' (stimes1 ∪ always1) ve0' ve0) as Hpre'.
        { apply in1_notin2_infer with (1:=Hpre); auto.
          now intros x ?; PS_split; destruct (PSP.In_dec x always2); intuition. }
        inversion_clear Hno as [| | | | |? ? Hwnw1 Hwnw2 Hno1 Hno2|].
        edestruct IHs1 as (ve1' & Henv1' & Heval1'); eauto.

        assert (in1_notin2 rq2 (stimes2 ∪ always2) ve1' ve1) as Hpre''.
        { pose proof (add_defaults_stmt_inv1 _ _ _ _ _ _ _ Hdefs1) as (HI1 & HI2 & HI3 & HI5).
          pose proof (add_defaults_stmt_inv2  _ _ _ _ _ _ _ _ _ _ Hcall Hdefs1 Heval1') as (HI6 & HI8); auto.
          now intros y Hyin; apply Hpre in Hyin.
          assert (H:=Hpre); apply in1_notin2_infer
            with (Z1 := rq2 \ always1) (Z2 := stimes2 ∪ always2)
            in H as (Hpre3 & Hpre4); [split| |].
          - intros x Hin.
            apply HI2, PS.union_spec in Hin as [Hin|Hin]; auto. apply Hpre in Hin.
            apply stmt_eval_mono with (1:=Heval1'); auto.
          - intros x Hin.
            pose proof (add_defaults_stmt_inv1 _ _ _ _ _ _ _ Hdefs2) as (H2A & H2B & H2C & H2E).
            specialize (H2C _ Hin); apply Hwnw2 in H2C.
            apply Hpre4 in Hin.
            eapply add_defaults_stmt_no_write in Hdefs1; eauto.
            now rewrite Env.Props.P.F.in_find_iff, Hdefs1, <-Env.Props.P.F.in_find_iff.
          - intros x Hin. apply PS.diff_spec in Hin as (Hin & Hnin).
            apply HI2, PS.union_spec in Hin as [Hin|Hin]; auto. contradiction.
          - intros x Hin. destruct (PSP.In_dec x always1). now intuition.
            PS_split; intuition. }

        edestruct IHs2 as (ve2' & Henv2' & Heval2'); eauto using stmt_eval.

      - (* Call ys clsid o f es *)
        simpl in *.
        rewrite (surjective_pairing (fold_right _ _ _)),
                 add_valid_add_valid', app_nil_r in Hadd.
        inv Hadd.
        match goal with H:Forall2 (exp_eval _ _) _ _ |- _ =>
          apply Forall2_exp_eval_refines_with_valid with (1:=Henv)
                          in H as (vos' & Heval1 & Hvos)
        end; eauto using in1_notin2_Var_In.
        match goal with H:stmt_call_eval _ _ _ _ _ _ _ |- _ =>
          apply program_refines_stmt_call_eval with (1:=Hpr) (4:=Hvos) in H
                          as (rvos' & Hcall' & Hrvos') end.
        { inv Hwt.
          exists (Env.adds_opt ys rvos' ve1); split; eauto using stmt_eval.
          apply Env.refines_adds_opt; auto.
          simpl in *.
          eapply in1_notin2_Var_Not_In; eauto.
        }

        assert (Forall (fun vo => vo <> None) vos') as Hsome.
        { apply Forall_forall. intros x Hin.
          apply Forall2_in_right with (1:=Heval1) in Hin as (e & Hin & Heval).
          apply in_map_iff in Hin as (e' & Hvalid & Hin).
          destruct e'; inv Heval;
            match goal with H:_ = add_valid' _ |- _ => inv H end; discriminate. }

        intros * Hfindc Hfindm Hlvos Hlvos'; split.
        + setoid_rewrite fst_InMembers.
          rewrite <-(map_length fst m.(m_in)) in Hlvos'.
          revert Hsome Hlvos'; clear; revert vos'.
          induction (map fst m.(m_in)) as [|x xs IH]; simpl.
          * unfold Env.adds_opt, vempty; simpl; split; intro; try contradiction.
            eapply Env.Props.P.F.empty_in_iff; eauto.
          * intros vos' Hsome Hlen.
            destruct vos'. discriminate.
            apply Forall_cons2 in Hsome as (Hvo & Hsome).
            apply not_None_is_Some in Hvo as (v & Hv); subst.
            inversion Hlen as [Hlen'].
            setoid_rewrite (IH _ Hsome Hlen').
            setoid_rewrite Env.Props.P.F.in_find_iff.
            intro y; split.
            intros [Hin|Hin]; subst.
            now rewrite Env.find_gsss_opt; discriminate.
            destruct (ident_eq_dec y x); subst.
            now rewrite Env.find_gsss_opt; discriminate.
            now rewrite Env.find_gsso_opt; auto.
            intros Hfind.
            destruct (ident_eq_dec y x); subst; auto.
            rewrite Env.find_gsso_opt in Hfind; auto.
        + intros; eapply fst_InMembers, Env.In_adds_opt_In; eauto.

      - (* Assign x e *)
        inv Hadd.
        exists (Env.add x (Vscalar rvo) ve1).
        split; eauto using Env.refines_add_both.
        econstructor; eauto; simpl_Forall; eauto using exp_eval_refines, stmt_eval.

      - (* skip *)
        inv Hadd; eauto using stmt_eval.
    Qed.

  End AddDefaultsStmt.


  Lemma output_or_local_in_typing_env:
    forall {A} (min mvars mout : list (ident * A)) S,
      NoDupMembers (min ++ mvars ++ mout) ->
      PS.For_all
        (fun x => PS.In x (PSP.of_list (map fst mout)) \/
                  InMembers x (min ++ mvars ++ mout)) S ->
      PS.For_all (fun x => Env.find x (Env.from_list (min ++ mvars ++ mout)) <> None)
                 (ps_removes (map fst min) S).
  Proof.
    intros A min mvars mout S Hmndup HS x Hin.
    apply ps_removes_spec in Hin as (Hnin & Hin).
    apply PS_In_Forall with (1:=HS) in Hin as [Hin|Hin].
    - apply ps_of_list_In in Hin.
      apply in_map_iff in Hin as ((y & yty) & Heq & Hin).
      do 2 (eapply or_intror, in_app in Hin).
      eapply Env.In_find_adds' in Hin; eauto.
      subst. apply not_None_is_Some; eauto.
    - apply InMembers_In in Hin as (xty & Hin).
      eapply Env.In_find_adds' in Hin; eauto.
      apply not_None_is_Some; eauto.
  Qed.

  Lemma stmt_call_eval_add_defaults_class_not_None:
    forall p,
      wt_program p ->
      forall ome ome' clsid f vos rvos,
        Forall (fun vo => vo <> None) vos ->
        stmt_call_eval (add_defaults p) ome clsid f vos ome' rvos ->
        Forall (fun x => x <> None) rvos.
  Proof.
    intros []; induction classes0 as [|c p' IH]; simpl. now inversion 3.
    intros WTp ome ome'' clsid f vos rvos Hvos Heval.
    inversion_clear WTp as [|?? [WTc Hpnd] WTp'].
    specialize (IH WTp').
    destruct (ident_eq_dec c.(c_name) clsid) as [He|Hne].
    - destruct c as (name, mems, objs, methods, Hnodup, Hnodupm, Hgood).
      simpl in *.
      inversion_clear Heval as [? ? ? ? ? ? ? ? ve'' ? ? Hfindc Hfindm Hlvos Heval' Hrvos].
      subst name. unfold add_defaults in Hfindc; simpl in Hfindc.
      eapply find_unit_cons in Hfindc as [[E Hfindc]|[E Hfindc]]; simpl in *; eauto; try contradiction.
      inv Hfindc. simpl in Hfindm.
      apply find_method_map_add_defaults_method' in Hfindm as (fm' & Hfindm' & Hfm').
      subst fm.
      inversion_clear WTc as [Hfao WTms]. clear Hfao; simpl in WTms.
      induction methods as [|m methods' IHm]; try discriminate.
      apply Forall_cons2 in WTms as (WTm & WTms).
      simpl in *; apply NoDup_cons' in Hnodupm as (Hnodupm1 & Hnodupm2).
      destruct (ident_eqb m.(m_name) f); [clear IHm|apply IHm; auto].
      clear Hnodupm1 Hnodupm2. inv Hfindm'.
      destruct fm' as (mname, min, mvars, mout, mbody, Hmndup, Hmgood).
      simpl in *.

      assert (Env.adds' mout (Env.adds' mvars (Env.from_list min))
              = Env.from_list (min ++ mvars ++ mout)) as Hpmeq
          by (now unfold Env.from_list; repeat rewrite Env.adds'_app).
      rewrite Hpmeq in Heval'; clear Hpmeq.

      remember (add_defaults_stmt
                  (fun x => Env.find x (Env.from_list (min ++ mvars ++ mout)))
                  (PSP.of_list (map fst mout)) mbody) as defs.
      symmetry in Heqdefs.
      setoid_rewrite Heqdefs in Heval'.
      destruct defs as [[[t req'] stimes] always].

      apply stmt_eval_add_writes_split in Heval' as (ome' & ve' & Heval & Heval').

      pose proof (add_defaults_stmt_inv1 _ _ _ _ _ _ _ Heqdefs)
        as (HH1 & Halreq' & HH2 & HH4); clear HH1 HH2.

      assert (forall x ty,
                 In (x, ty) (min ++ mvars ++ mout) <->
                 Env.find x (Env.from_list (min ++ mvars ++ mout)) = Some ty) as Hinf
          by (split; [apply Env.In_find_adds'|apply Env.from_list_find_In]; auto).

      apply wt_method_add_defaults in WTm.
      unfold wt_method, meth_vars in WTm; simpl in WTm.
      destruct WTm as (WTm & Henums).
      change types0 with (types (add_defaults {| types := types0; externs := externs0; classes := p' |})) in Henums.

      pose proof (add_defaults_stmt_wt _ _ _ _ _ Hinf Henums _ _ _ _ _ _ Heqdefs WTm)
          as (WTt & WTst & WTal & Hreq').

      assert (forall x, x ∈ (ps_removes (map fst min) req') -> Env.In x ve')
        as Hreq'in
          by (intros y Hin; apply stmt_eval_add_writes in Heval;
              auto using output_or_local_in_typing_env).

      eapply add_defaults_stmt_inv2 in Heqdefs as (Hstal & Hal); eauto.
      + apply Forall_forall; intros y Hin.
        apply Forall2_in_right with (1:=Hrvos) in Hin as (xo & Hin & Hfind).
        assert (~In xo (map fst min)) as Hnmin.
        { intros Hin'. apply fst_InMembers in Hin'.
          apply fst_InMembers in Hin.
          apply NoDupMembers_app_InMembers with (1:=Hmndup) in Hin'.
          apply Hin', InMembers_app; auto. }
        eapply ps_of_list_In, Halreq', PS.union_spec in Hin as [Hin|Hin].
        * apply Hal, Env.Props.P.F.in_find_iff in Hin. now rewrite Hfind in Hin.
        * apply (conj Hnmin), ps_removes_spec, Hreq'in in Hin.
          apply stmt_eval_mono with (1:=Heval') in Hin; auto.
          now apply Env.Props.P.F.in_find_iff in Hin; rewrite Hfind in Hin.
      + intros y Hin.
        destruct (In_dec ident_eq_dec y (map fst min)) as [Him|Hnim].
        * cut (Env.In y (Env.adds_opt (map fst min) vos vempty)).
          intro Hii; apply stmt_eval_mono with (1:=Heval) in Hii; auto.
          revert Him Hvos Hlvos; clear.
          rewrite <-(map_length fst). revert vos.
          induction (map fst min) as [|y' ys IH].
          now intros vos Him; apply in_nil in Him.
          intros vos Him Hvos Hlvos.
          destruct vos as [|vo vos]. discriminate.
          apply Forall_cons2 in Hvos as (Hvo & Hvos).
          apply not_None_is_Some in Hvo as (v & Hvo); subst.
          apply Env.Props.P.F.in_find_iff.
          inv Him. now rewrite Env.find_gsss_opt. inv Hlvos.
          destruct (ident_eq_dec y y'). now subst; rewrite Env.find_gsss_opt.
          rewrite Env.find_gsso_opt; simpl; auto.
          apply Env.Props.P.F.in_find_iff; auto.
        * now apply (conj Hnim), ps_removes_spec, Hreq'in in Hin.
    - assert ((add_defaults_class c).(c_name) <> clsid) as Hne'
          by (destruct c; auto).
      unfold add_defaults in Heval; simpl in Heval.
      rewrite stmt_call_eval_cons in Heval; eauto.
  Qed.

  Lemma wt_add_defaults_method:
    forall p objs mems m,
      wt_method p objs mems m ->
      wt_method p objs mems (add_defaults_method m).
  Proof.
    unfold wt_method, meth_vars.
    intros p objs mems m (WTm & Henums).
    rewrite add_defaults_method_m_in,
            add_defaults_method_m_out,
            add_defaults_method_m_vars.
    split; auto.
    destruct m as [n min mvars mout s Hnodup Hgood]; simpl in *.

    assert (Env.adds' mout (Env.adds' mvars (Env.from_list min))
            = Env.from_list (min ++ mvars ++ mout)) as Hpmeq
        by (now unfold Env.from_list; repeat rewrite Env.adds'_app).
    rewrite Hpmeq; clear Hpmeq.

    remember (add_defaults_stmt
                (fun x => Env.find x (Env.from_list (min ++ mvars ++ mout)))
                (PSP.of_list (map fst mout)) s) as defs.
    symmetry in Heqdefs.
    setoid_rewrite Heqdefs.
    destruct defs as [[[t req'] stimes] always].

    assert (forall x ty,
               In (x, ty) (min ++ mvars ++ mout) <->
               Env.find x (Env.from_list (min ++ mvars ++ mout)) = Some ty) as Hinf
        by (split; [apply Env.In_find_adds'|apply Env.from_list_find_In]; auto).

    eapply add_defaults_stmt_wt with (1:=Hinf) (2:=Henums) (3:=Heqdefs) in WTm.
    destruct WTm as (WTt & HH1 & HH2 & Hreq'); clear HH1 HH2.

    apply add_writes_wt; auto.
    apply output_or_local_in_typing_env; auto.
  Qed.

  Lemma wt_memory_add_defaults:
    forall p c me,
      wt_memory me p c.(c_mems) c.(c_objs) ->
      wt_memory me (add_defaults p) (add_defaults_class c).(c_mems) (add_defaults_class c).(c_objs).
  Proof.
    intros * WT.
    (* TODO: why a direct apply does not work? *)
    pose proof transform_units_wt_memory' as Spec; simpl in Spec.
    eapply Spec in WT; auto.
  Qed.

  Lemma wt_add_defaults_class:
    forall p,
      wt_program p ->
      wt_program (add_defaults p).
  Proof.
    intros; eapply transform_units_wt_program; eauto.
    inversion_clear 1 as [Hfobs WTms].
    constructor; auto.
    - rewrite add_defaults_class_c_objs.
      apply Forall_impl_In with (2:=Hfobs).
      intros * ? Find.  apply find_class_add_defaults_class_not_None in Find; auto.
    - rewrite add_defaults_class_c_mems, add_defaults_class_c_objs.
      destruct u as (name, mems, objs, methods, Hnodup, Hnodupm, Hgood); simpl in *.
      apply Forall_map, Forall_impl_In with (2:=WTms).
      intros m Him WTm. apply wt_method_add_defaults in WTm.
      now apply wt_add_defaults_method.
  Qed.

  Lemma add_defaults_stmt_refines:
    forall p1 p2 insts mems m,
      program_refines (fun _ _ => all_in1) p1 p2 ->
      wt_method p2 insts mems m ->
      No_Overwrites m.(m_body) ->
      Forall (fun x => ~Can_write_in x m.(m_body)) (map fst m.(m_in)) ->
      (forall ome ome' clsid f vos rvos,
          Forall (fun vo => vo <> None) vos ->
          stmt_call_eval p1 ome clsid f vos ome' rvos ->
          Forall (fun x => x <> None) rvos) ->
      stmt_refines p1 p2
                   (in1_notin2 (PSP.of_list (map fst m.(m_in)))
                               (PSP.of_list (map fst (m.(m_out) ++ m.(m_vars)))))
                   (add_defaults_method m).(m_body) m.(m_body).
  Proof.
    unfold wt_method, meth_vars; intros p1 p2 insts mems m Hpr WT;
      destruct m as [n ins vars outs s nodup good]; simpl in *.
    unfold Env.from_list; repeat rewrite Env.adds'_app;
      fold (@Env.from_list type (outs ++ vars ++ ins)).
    match goal with |- context [ add_defaults_stmt ?tyenv ?W s ] =>
      set (defs := add_defaults_stmt tyenv W s);
        assert (add_defaults_stmt tyenv W s = defs) as Hdefs by now subst defs
    end.
    destruct defs as [[[t rq'] st] al].
    intros Hnoo Hncwin Hcall me ve1' ve1 me' ve2 Hpre Henv Heval.
    destruct WT as (WT & Henums).
    apply wt_stmt_program_refines with (1:=Hpr) in WT.
    erewrite <-program_refines_types in Henums; eauto.

    assert (forall x ty,
      In (x, ty) (ins ++ vars ++ outs) <->
      Env.find x (Env.adds' (ins ++ vars ++ outs) (Env.empty _)) = Some ty)
      as Htyenv.
    { split; intro HH.
      now apply Env.In_find_adds'.
      now apply Env.from_list_find_In in HH. }

    assert (WT':=WT); eapply add_defaults_stmt_wt with (1:=Htyenv) (2:=Henums) (3:=Hdefs) in WT'
      as (WTt & Hvst & Hval & Hrq').

    assert (PS.For_all (fun x => InMembers x (ins ++ vars ++ outs))
                       (ps_removes (map fst ins) rq')) as Hrq''.
    { intros x Hin.
      apply ps_removes_spec in Hin as (Hnin & Hin).
      apply PS_In_Forall with (1:=Hrq') in Hin as [Hin|Hin]; auto.
      do 2 (apply InMembers_app; right). apply fst_InMembers.
      apply ps_of_list_In in Hin; auto. }

    destruct Hpre as (Hpre1 & Hpre2).
    assert (PS.For_all (fun x => ~Env.In x ve1) (ps_removes (map fst ins) rq')).
    { intros x Hin.
      apply PS_In_Forall with (2:=Hin) in Hrq''.
      apply Hpre2. rewrite <-ps_adds_of_list.
      apply ps_adds_spec; left; apply fst_InMembers.
      setoid_rewrite (Permutation.Permutation_app_comm outs vars).
      apply InMembers_app in Hrq'' as [Hrq''|Hrq'']; auto.
      apply ps_removes_spec in Hin as (Hnin & Hin).
      apply fst_InMembers in Hrq''; contradiction. }

    eapply stmt_eval_add_writes_Skip with (1:=Htyenv) (p:=p1) (me:=me)
                                          (w:=ps_removes (map fst ins) rq')
      in Henv as (ve2' & Henv2' & Heval2' & Hmono2 & Hin2'); eauto.

    assert (Hsr:=Hdefs); eapply add_defaults_stmt_correct in Hsr; eauto.

    pose proof (add_defaults_stmt_inv1 _ _ _ _ _ _ _ Hdefs)
      as (HI1 & HI2 & HI3 & HI4).

    assert (in1_notin2 rq' (st ∪ al) ve2' ve1) as Hinout.
    { split.
      - intros x Hin.
        destruct (In_dec ident_eq_dec x (map fst ins)) as [Hiin|].
        + apply Hmono2, Hpre1, PSP.of_list_1, SetoidList.InA_alt; eauto.
        + assert (x ∈ (ps_removes (map fst ins) rq')) as Hinrq'
              by (apply ps_removes_spec; auto).
          now apply PS_In_Forall with (1:=Hin2') in Hinrq'.
      - intros x Hin.
        apply Hpre2, PSP.of_list_1, Env.ME.MO.ListIn_In, fst_InMembers.
        specialize (HI3 _ Hin).
        setoid_rewrite (Permutation.Permutation_app_comm outs vars).
        apply PS.union_spec in Hin as [Hin|Hin].
        + apply PS_In_Forall with (1:=Hvst) in Hin.
          apply InMembers_app in Hin.
          destruct Hin as [Hin|]; auto.
          apply InMembers_Forall with (1:=Hncwin) in Hin.
          exfalso; auto with obcinv.
        + apply PS_In_Forall with (1:=Hval) in Hin.
          apply InMembers_app in Hin.
          destruct Hin as [Hin|]; auto.
          apply InMembers_Forall with (1:=Hncwin) in Hin.
          exfalso; auto with obcinv. }

    eapply Hsr in Heval as (ve3' & Henv3' & Heval3'); eauto.

    exists ve3'; split; auto.
    apply stmt_eval_add_writes_split; eauto.
  Qed.

  Lemma No_Naked_Vars_add_defaults_method:
    forall m, No_Naked_Vars (add_defaults_method m).(m_body).
  Proof.
    destruct m as [n ins vars outs s nodup good]; simpl.
    match goal with |- context [ add_defaults_stmt ?tyenv ?W s ] =>
      set (defs := add_defaults_stmt tyenv W s);
        assert (add_defaults_stmt tyenv W s = defs) as Hdefs by now subst defs
    end.
    destruct defs as [[[t rq'] st] al].
    pose proof (add_defaults_stmt_inv1 _ _ _ _ _ _ _ Hdefs)
      as (HI1 & HI2 & HI3 & HI5).
    now apply No_Naked_Vars_add_writes.
  Qed.

  Lemma add_defaults_method_refines:
    forall p1 p2 insts mems m,
      program_refines (fun _ _ => all_in1) p1 p2 ->
      wt_method p2 insts mems m ->
      No_Overwrites m.(m_body) ->
      Forall (fun x => ~ Can_write_in x m.(m_body)) (map fst m.(m_in)) ->
      (forall ome ome' clsid f vos rvos,
          Forall (fun vo => vo <> None) vos ->
          stmt_call_eval p1 ome clsid f vos ome' rvos ->
          Forall (fun x => x <> None) rvos) ->
      method_refines p1 p2 all_in1 (add_defaults_method m) m.
  Proof.
    intros * Hpr WTm Hnoo Hncwi Hcall.
    unfold method_refines.
    rewrite add_defaults_method_m_in, add_defaults_method_m_out.
    repeat split; auto.
    eapply add_defaults_stmt_refines
      with (2:=WTm) (3:=Hnoo) (4:=Hncwi) (5:=Hcall) in Hpr.
    apply stmt_refines_strengthen with (1:=Hpr).
    intros ve1 ve2 (Hpre1 & Hpre2).
    split; setoid_rewrite In_of_list_InMembers.
    now apply Hpre1.
    intros x Hin.
    rewrite Permutation.Permutation_app_comm in Hin.
    apply NoDupMembers_app_InMembers with (ws:=m.(m_in)) in Hin; auto.
    rewrite Permutation.Permutation_app_comm. apply m_nodupvars.
  Qed.

  Lemma add_defaults_class_refines:
    forall p1 p2 c,
      program_refines (fun _ _ => all_in1) p1 p2 ->
      wt_class p2 c ->
      Forall (fun m => No_Overwrites m.(m_body)) c.(c_methods) ->
      Forall (fun m => Forall (fun x => ~ Can_write_in x m.(m_body))
                              (map fst m.(m_in))) c.(c_methods) ->
      (forall ome ome' clsid f vos rvos,
          Forall (fun vo => vo <> None) vos ->
          stmt_call_eval p1 ome clsid f vos ome' rvos ->
          Forall (fun x => x <> None) rvos) ->
      class_refines p1 p2 (fun _ => all_in1) (add_defaults_class c) c.
  Proof.
    intros p1 p2 c Hpr WTc Hnoo Hncwm Hcall f fm Hfind.
    apply wt_class_find_method with (2:=Hfind) in WTc.
    rewrite add_defaults_class_find_method, Hfind; simpl.
    pose proof (find_method_In _ _ _ Hfind) as Hin.
    exists (add_defaults_method fm). split; auto.
    apply Forall_forall with (2:=Hin) in Hnoo.
    apply Forall_forall with (2:=Hin) in Hncwm.
    eapply add_defaults_method_refines; eauto.
  Qed.

  Lemma add_defaults_program_refines:
    forall p,
      wt_program p ->
      Forall_methods (fun m => No_Overwrites m.(m_body)) p ->
      Forall_methods (fun m => Forall (fun x => ~ Can_write_in x m.(m_body))
                                      (map fst m.(m_in))) p ->
      program_refines (fun _ _ => all_in1) (add_defaults p) p.
  Proof.
    intros p WTp Hnoo Hncw.
    cut (Forall2 (fun c1 c2 => c1 = add_defaults_class c2)
                 (add_defaults p).(classes) p.(classes)).
    2:now apply Forall2_map_1, Forall2_same, Forall_forall.
    apply program_refines_by_class' with (1:=WTp); auto.
    apply all_In_Forall2.
    now unfold add_defaults; simpl; rewrite map_length.
    intros c1 c2 Hin p1' p2' WTp' WTc Hpr Hadc Hx; subst.
    rewrite add_defaults_class_c_name; split; auto.
    apply in_combine_r in Hin.
    apply Forall_forall with (2:=Hin) in Hnoo.
    apply Forall_forall with (2:=Hin) in Hncw.
    apply add_defaults_class_refines with (1:=Hpr); auto.
    assert (p1' = add_defaults p2') as Hp1'.
    { destruct p1', p2'; unfold add_defaults; simpl; f_equal.
      - apply program_refines_def in Hpr as (?&?); auto.
      - apply program_refines_def in Hpr as (?&?&?); auto.
      - simpl in Hadc. clear Hpr WTp' WTc; induction Hadc; auto; subst; simpl; auto.
    }
    subst. now apply stmt_call_eval_add_defaults_class_not_None.
  Qed.

  Lemma No_Naked_Vars_add_defaults_class:
    forall p,
      Forall_methods (fun m => No_Naked_Vars m.(m_body)) (add_defaults p).
  Proof.
    intros p.
    apply Forall_forall; intros c' Hcin.
    unfold add_defaults in *; apply in_map_iff in Hcin as (c & Hc' & Hcin); subst.
    apply Forall_forall; intros m' Hmin.
    destruct c as (name, mems, objs, methods, Hnodup, Hnodupm, Hgood); simpl in *.
    apply in_map_iff in Hmin as (m & Hm & Hmin); subst.
    apply No_Naked_Vars_add_defaults_method.
  Qed.

  Theorem stmt_call_eval_add_defaults:
    forall p me f m vs me' rvs,
      wt_program p ->
      Forall_methods (fun m => No_Overwrites m.(m_body)) p ->
      Forall_methods (fun m => Forall (fun x => ~ Can_write_in x m.(m_body))
                                      (map fst m.(m_in))) p ->
      stmt_call_eval p me f m (map Some vs) me' (map Some rvs) ->
      stmt_call_eval (add_defaults p) me f m (map Some vs) me' (map Some rvs).
  Proof.
    intros * WTp NOO NCW Call.
    eapply program_refines_stmt_call_eval in Call as (rvos &?& Spec);
      eauto using add_defaults_program_refines.
    - assert (rvos = map Some rvs) as ->; eauto.
      rewrite Forall2_map_2 in Spec.
      clear - Spec; induction Spec; simpl; auto; f_equal; auto.
    - split;
        rewrite Env.adds_opt_is_adds; try apply fst_NoDupMembers, m_nodupin; intro;
          rewrite Env.In_adds_spec, fst_InMembers, Env.Props.P.F.empty_in_iff; intuition;
            now rewrite map_length in *.
    - apply Forall2_same, Forall_forall; auto.
  Qed.

  Corollary loop_call_add_defaults:
    forall f c ins outs p me,
      wt_program p ->
      Forall_methods (fun m => No_Overwrites m.(m_body)) p ->
      Forall_methods (fun m => Forall (fun x => ~ Can_write_in x m.(m_body))
                                      (map fst m.(m_in))) p ->
      loop_call p c f (fun n => map Some (ins n)) (fun n => map Some (outs n)) 0 me ->
      loop_call (add_defaults p) c f (fun n => map Some (ins n)) (fun n => map Some (outs n)) 0 me.
  Proof.
    intros ?????; generalize 0%nat.
    cofix COINDHYP.
    intros n me WTp NOO NCW Hdo.
    destruct Hdo.
    econstructor; eauto using stmt_call_eval_add_defaults.
  Qed.

End OBCADDDEFAULTS.

Module ObcAddDefaultsFun
       (Ids   : IDS)
       (Op    : OPERATORS)
       (OpAux : OPERATORS_AUX Ids Op)
       (SynObc: OBCSYNTAX     Ids Op OpAux)
       (ComTyp: COMMONTYPING  Ids Op OpAux)
       (SemObc: OBCSEMANTICS  Ids Op OpAux SynObc)
       (InvObc: OBCINVARIANTS Ids Op OpAux SynObc        SemObc)
       (TypObc: OBCTYPING     Ids Op OpAux SynObc ComTyp SemObc)
       (Equ   : EQUIV         Ids Op OpAux SynObc ComTyp SemObc TypObc)
       <: OBCADDDEFAULTS Ids Op OpAux SynObc ComTyp SemObc InvObc TypObc Equ.
  Include OBCADDDEFAULTS Ids Op OpAux SynObc ComTyp SemObc InvObc TypObc Equ.
End ObcAddDefaultsFun.
