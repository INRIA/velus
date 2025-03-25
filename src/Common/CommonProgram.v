(* *********************************************************************)
(*                                                                     *)
(*                 The Vélus verified Lustre compiler                  *)
(*                                                                     *)
(*             (c) 2019 Inria Paris (see the AUTHORS file)             *)
(*                                                                     *)
(*  Copyright Institut National de Recherche en Informatique et en     *)
(*  Automatique. All rights reserved. This file is distributed under   *)
(*  the terms of the INRIA Non-Commercial License Agreement (see the   *)
(*  LICENSE file).                                                     *)
(*                                                                     *)
(* *********************************************************************)

From Velus Require Import Common.

From Coq Require Import List.
From Coq Require Import Permutation.
Import List.ListNotations.

Class ProgramUnit (U: Type) := { name: U -> ident }.

Class ProgramStateUnit (U T: Type) :=
  { ProgramStateUnitProgramUnit :: ProgramUnit U;
    state_variables    : U -> list (ident * T);
    instance_variables : U -> list (ident * ident)
  }.

Section Program.

  Class Program (U Prog: Type) :=
    { units  : Prog -> list U;
      update : Prog -> list U -> Prog;

      units_of_update :
        forall p us,
          units (update p us) = us;

      update_idempotent :
        forall p us us',
          update (update p us) us' = update p us';
    }.

  Context {U Prog: Type}.
  Context `{ProgramUnit U} `{Program U Prog}.

  Definition find_unit (f: ident) (p: Prog) : option (U * Prog):=
    let fix find p :=
        match p with
        | [] => None
        | u :: p =>
          if ident_eq_dec (name u) f
          then Some (u, p) else find p
        end
    in
    match find (units p) with
    | Some (u, us) => Some (u, update p us)
    | None => None
   end.

  Lemma find_unit_empty:
    forall f p,
      units p = [] ->
      find_unit f p = None.
  Proof.
    unfold find_unit; intros * ->; reflexivity.
  Qed.

  Definition ltsuffix_prog (p p': Prog) := ltsuffix (units p) (units p').

  Lemma ltsuffix_prog_wf: well_founded ltsuffix_prog.
  Proof.
    unfold ltsuffix_prog.
    pose proof (@ltsuffix_wf U) as WF.
    apply Wf.measure_wf with (m := units) in WF; auto.
  Qed.

  Lemma find_unit_ltsuffix_prog:
    forall f p u p',
      find_unit f p = Some (u, p') ->
      ltsuffix_prog p' p.
  Proof.
    unfold find_unit, ltsuffix_prog; intros * Find.
    induction (units p) as [|u']; try discriminate.
    destruct (ident_eq_dec (name u') f).
    - inv Find.
      rewrite units_of_update.
      apply ltsuffix_cons.
    - destruct IHl as (?&?&?); auto.
      subst.
      eexists; intuition; eauto; discriminate.
  Qed.

  Lemma program_ind:
    forall (P: Prog -> Prop),
      (forall p,
          (forall f u p',
              find_unit f p = Some (u, p') ->
              P p') ->
          P p) ->
      forall p, P p.
  Proof.
    intros * SomeCase ?; eapply well_founded_induction with (1 := ltsuffix_prog_wf).
    intros * IH.
    apply SomeCase; intros * Find.
    eapply IH, find_unit_ltsuffix_prog; eauto.
  Qed.

  Definition equiv_program (p p': Prog) :=
    forall us, update p us = update p' us.

  Lemma equiv_program_refl:
    forall p, equiv_program p p.
  Proof.
    intros ??; reflexivity.
  Qed.

  Lemma equiv_program_sym:
    forall p p', equiv_program p p' -> equiv_program p' p.
  Proof.
    intros * ??; auto.
  Qed.

  Lemma equiv_program_trans:
    forall p p' p'', equiv_program p p' -> equiv_program p' p'' -> equiv_program p p''.
  Proof.
    intros * ???; etransitivity; eauto.
  Qed.

  (* Global does not seem to work... *)
  Global Add Parametric Relation: Prog equiv_program
      reflexivity proved by equiv_program_refl
      symmetry proved by equiv_program_sym
      transitivity proved by equiv_program_trans
        as program_equiv_rel.

  Lemma equiv_program_update:
    forall p us,
      equiv_program p (update p us).
  Proof.
    intros ?? us'.
    now rewrite update_idempotent.
  Qed.

  Lemma find_unit_equiv_program:
    forall p f u p',
      find_unit f p = Some (u, p') ->
      equiv_program p p'.
  Proof.
    unfold find_unit.
    intro; induction (units p); intros * Find us; try discriminate.
    cases; inv Find.
    now rewrite update_idempotent.
  Qed.

  Lemma find_unit_now: forall p u us,
      units p = u :: us ->
      find_unit (name u) p = Some (u, update p us).
  Proof.
    intros * Hunits.
    unfold find_unit. rewrite Hunits; simpl.
    destruct (ident_eq_dec _ _); try congruence.
  Qed.

  Lemma find_unit_later:
    forall f p us p',
      equiv_program p p' ->
      units p = us ++ units p' ->
      Forall (fun u => f <> name u) us ->
      (find_unit f p = find_unit f p').
  Proof.
    intros * Eq E Hnf.
    unfold find_unit; rewrite E; simpl.
    revert dependent p; revert p'.
    induction Hnf as [|u us']; intros; simpl in *; auto.
    - cases; rewrite Eq; auto.
    - erewrite <-IHHnf with (p := update p (us' ++ units p')); eauto.
      + destruct (ident_eq_dec (name u) f); subst; try contradiction.
        cases; rewrite update_idempotent; auto.
      + intro; rewrite update_idempotent, Eq; auto.
      + now rewrite units_of_update.
  Qed.

  Lemma find_unit_other:
    forall f u p p',
      equiv_program p p' ->
      name u <> f ->
      units p = u :: units p' ->
      (find_unit f p = find_unit f p').
  Proof.
    intros * Eq Hnf E.
    unfold find_unit; rewrite E; simpl.
    destruct (ident_eq_dec (name u) f); try contradiction.
    cases; now rewrite Eq.
  Qed.

  Lemma find_unit_In:
    forall p f u p',
      find_unit f p = Some (u, p') ->
      name u = f /\ In u (units p).
  Proof.
    intro; unfold find_unit.
    induction (units p) as [|u]; try discriminate.
    intros * Find.
    destruct (ident_eq_dec (name u) f).
    - inv Find; intuition.
    - apply IHl in Find; intuition.
  Qed.

  Lemma find_unit_Exists:
    forall f p, find_unit f p <> None <-> Exists (fun u => f = (name u)) (units p).
  Proof.
    intros; unfold find_unit.
    induction (units p) as [|u].
    - rewrite Exists_nil; intuition.
    - destruct (ident_eq_dec (name u) f).
      + split; try discriminate.
        now constructor.
      + rewrite IHl, Exists_cons; intuition.
  Qed.

  Remark In_find_unit:
    forall p u,
      NoDup (map name (units p)) ->
      In u (units p) ->
      exists p', find_unit (name u) p = Some (u, p').
  Proof.
    intros * Nodup Hin; unfold find_unit.
    induction (units p) as [|u' p']; try contradiction.
    simpl in Nodup; inversion_clear Nodup as [|?? Hnin].
    inv Hin.
    - destruct (ident_eq_dec (name u) (name u)); eauto; contradiction.
    - destruct (ident_eq_dec (name u') (name u)); eauto.
      exfalso.
      apply Hnin.
      rewrite e; apply in_map; auto.
  Qed.

  Lemma find_unit_spec:
    forall f p u p',
      find_unit f p = Some (u, p') ->
      name u = f
      /\ exists us,
          units p = us ++ u :: units p'
          /\ Forall (fun u => f <> name u) us.
  Proof.
    unfold find_unit; intros * Find.
    induction (units p) as [|u']; try discriminate.
    destruct (ident_eq_dec (name u') f).
    - inv Find; intuition.
      exists nil; simpl; rewrite units_of_update; intuition.
    - apply IHl in Find as (?& us & -> &?).
      intuition.
      exists (u' :: us); intuition.
  Qed.

  Lemma find_unit_None:
    forall p f,
      find_unit f p = None <-> Forall (fun u => f <> name u) (units p).
  Proof.
    unfold find_unit; intros.
    induction (units p) as [|u]; [intuition|].
    destruct (ident_eq_dec (name u) f); rewrite Forall_cons2.
    - split; try discriminate; intuition.
    - intuition.
  Qed.

  Lemma find_unit_Some:
    forall f p u p',
      find_unit f p = Some (u, p') <->
      (exists us,
          units p = u :: us
          /\ p' = update p us
          /\ name u = f)
      \/
      (exists u' us,
          units p = u' :: us
          /\ name u' <> f
          /\ find_unit f (update p us) = Some (u, p')).
  Proof.
    unfold find_unit; intros ??.
    induction (units p) as [|u']; simpl.
    - split; try discriminate.
      intros [(?&?&?)|(?&?&?&?&?)]; discriminate.
    - intros.
      destruct (ident_eq_dec (name u') f); simpl.
      + split.
        * intros E; inv E; intuition eauto.
        * intros [(?& E &?&?)|(?&?& E & ?&?)]; inv E; auto; contradiction.
      + split.
        * rewrite IHl; setoid_rewrite units_of_update.
          intros [(us & E &?&?)|(u'' & us & E &?&?)]; inv E.
          -- right; exists u', (u :: us); intuition.
             destruct (ident_eq_dec (name u) (name u)); try contradiction.
             now rewrite update_idempotent.
          -- right; exists u', (u'' :: us); intuition.
             destruct (ident_eq_dec (name u'') f); try contradiction.
             cases; now rewrite update_idempotent in *.
        * intros [(us & E &?&?)|(u'' & us & E &?& Find)]; inv E.
          -- contradiction.
          -- rewrite units_of_update in Find.
             cases; now rewrite update_idempotent in Find.
  Qed.

  Lemma find_unit_app:
    forall f p us us',
      units p = us ++ us' ->
      find_unit f p =
      match find_unit f (update p us) with
      | None => find_unit f (update p us')
      | Some (u, p') => Some (u, update p (units p' ++ us'))
      end.
  Proof.
    unfold find_unit; intros * ->.
    rewrite ? units_of_update.
    induction us as [|u]; simpl in *.
    - cases; now rewrite update_idempotent.
    - destruct (ident_eq_dec (name u) f); simpl.
      + now rewrite update_idempotent, units_of_update.
      + rewrite IHus.
        destruct ((fix find (p0 : list U) : option (U * list U) :=
                     match p0 with
                     | [] => None
                     | u0 :: p1 => if ident_eq_dec (name u0) f then Some (u0, p1) else find p1
                     end) us) as [[]|]; auto.
        now rewrite ? update_idempotent, units_of_update.
  Qed.

  Lemma find_unit_cons:
    forall f p u us up',
      units p = u :: us ->
      find_unit f p = up' <->
      (f = name u /\ up' = Some (u, update p us))
      \/ (f <> name u /\ find_unit f (update p us) = up').
  Proof.
    unfold find_unit.
    intros * ->.
    setoid_rewrite units_of_update.
    destruct (ident_eq_dec (name u) f).
    - split; intuition.
    - split.
      + right; intuition.
        cases; now rewrite update_idempotent.
      + intros [[]|[? Find]]; try congruence.
        cases; now rewrite update_idempotent in Find.
  Qed.

  Section Suffix.

    Inductive suffix: Prog -> Prog -> Prop :=
      suffix_intro: forall p p' us,
        equiv_program p p' ->
        units p' = us ++ units p ->
        suffix p p'.

    Lemma suffix_refl:
      forall p, suffix p p.
    Proof.
      econstructor; auto using equiv_program_refl.
      now rewrite app_nil_l.
    Qed.

    Global Add Parametric Relation: Prog suffix
        reflexivity proved by suffix_refl
          as suffix_rel.

    Lemma suffix_cons:
      forall u p p' p'',
        equiv_program p p'' ->
        units p = u :: units p'' ->
        suffix p p' ->
        suffix p'' p'.
    Proof.
      intros * E E' Hsub; inv Hsub.
      econstructor.
      - symmetry in E; transitivity p; auto.
      - take (units p' = _) and rewrite it.
        rewrite E', <-app_last_app; eauto.
    Qed.

    Lemma find_unit_suffix:
      forall p f u p',
        find_unit f p = Some (u, p') ->
        suffix p' p.
    Proof.
      intros * Find.
      assert (equiv_program p' p) by (symmetry; eapply find_unit_equiv_program; eauto).
      apply find_unit_spec in Find as (?&?& E &?).
      rewrite <-app_last_app in E.
      econstructor; eauto.
    Qed.

  End Suffix.

  Section Ordered.

    Variable Is_called_in: ident -> U -> Prop.

    Definition Ordered_program (p: Prog) :=
      Forall' (fun us u =>
                 (forall f,
                     Is_called_in f u ->
                     f <> name u
                     /\ exists u' p', find_unit f (update p us) = Some (u', p'))
                 /\ Forall (fun u' => name u <> name u') us)
              (units p).

    Lemma Ordered_program_append:
      forall p us p',
        equiv_program p p' ->
        units p = us ++ units p' ->
        Ordered_program p ->
        Forall' (fun us u => Forall (fun u' => name u <> name u') (us ++ units p')) us
        /\ Ordered_program p'.
    Proof.
      unfold Ordered_program; intros * E -> Ord; split.
      - induction us; simpl.
        + constructor.
        + rewrite <-app_comm_cons in Ord.
          inversion_clear Ord as [|?? [] Ord'].
          apply IHus in Ord'.
          constructor; auto.
      - apply Forall'_app_r in Ord.
        eapply Forall'_impl; eauto; simpl; intros * (Spec &?); split; auto.
        intros * Called; apply Spec in Called as (?&?&?& Find); intuition.
        rewrite <-E; eauto.
    Qed.

    Corollary Ordered_program_append':
      forall p us us',
        units p = us ++ us' ->
        Ordered_program p ->
        Forall' (fun us u => Forall (fun u' => name u <> name u') (us ++ us')) us
        /\ Ordered_program (update p us').
    Proof.
      intros * E Ord.
      assert (units p = us ++ units (update p us')) by now rewrite units_of_update.
      clear E; eapply Ordered_program_append in Ord as (?&?); eauto.
      - split; auto.
        eapply Forall'_impl; eauto; simpl.
        now setoid_rewrite units_of_update.
      - apply equiv_program_update.
    Qed.

    Lemma Ordered_program_find_unit:
      forall p f u p',
        Ordered_program p ->
        find_unit f p = Some (u, p') ->
        Ordered_program (update p (u :: units p')).
    Proof.
      intros * Ord Find.
      pose proof Find as Eq; apply find_unit_equiv_program in Eq.
      apply find_unit_spec in Find as (?&?&?&?).
      eapply Ordered_program_append' in Ord as (?& Ord); eauto.
    Qed.

    Lemma not_Is_called_in_self:
      forall p f u p',
        Ordered_program p ->
        find_unit f p = Some (u, p') ->
        ~ Is_called_in f u.
    Proof.
      unfold find_unit; induction 1 as [|u' ? (Spec & ?)]; try discriminate.
      destruct (ident_eq_dec (name u') f); auto.
      intros E Called; inv E.
      apply Spec in Called as []; contradiction.
    Qed.

    Lemma find_unit_later_not_Is_called_in:
      forall f' us p p' u' p'',
        Ordered_program p ->
        units p = us ++ units p' ->
        find_unit f' p' = Some (u', p'') ->
        Forall (fun u => ~ Is_called_in (name u) u') us.
    Proof.
      intros * Ord E Find'.
      apply find_unit_spec in Find' as (?& us' & E' &?).
      rewrite E' in E.
      pose proof Ord as Ord'.
      eapply Ordered_program_append' in Ord as (Ndp & Ord); eauto.
      rewrite app_assoc in E.
      eapply Ordered_program_append' in Ord' as (Ndp' & Ord'); eauto.
      unfold Ordered_program in Ord; rewrite units_of_update in Ord.
      unfold Ordered_program in Ord'; rewrite units_of_update in Ord'.
      inversion_clear Ord' as [|?? (Spec &?)].
      apply Forall_forall; intros * Hin Called.
      apply Spec in Called as (?&?&?& Find).
      rewrite update_idempotent in Find.
      apply find_unit_In in Find as (?& Hin').
      rewrite units_of_update in Hin'.
      eapply Forall'_In in Ndp as (?&?&?& Ndp); eauto.
      rewrite 2 Forall_app, Forall_cons2 in Ndp.
      destruct Ndp as (?&?&?& Ndp).
      eapply Forall_forall with (2 := Hin') in Ndp; eauto.
    Qed.

    Corollary find_unit_other_not_Is_called_in:
      forall f' u p p' u' p'',
        Ordered_program p ->
        units p = u :: units p' ->
        find_unit f' p' = Some (u', p'') ->
        ~ Is_called_in (name u) u'.
    Proof.
      intros * Ord E Find.
      rewrite cons_is_app in E.
      eapply find_unit_later_not_Is_called_in in Find; eauto.
      now inv Find.
    Qed.

    Lemma find_unit_not_Is_called_in:
      forall p f u p' g,
        Ordered_program p ->
        find_unit g p = None ->
        find_unit f p = Some (u, p') ->
        ~ Is_called_in g u.
    Proof.
      intros * Ord Findg Findf.
      apply find_unit_spec in Findf as (?& us & E &?).
      eapply Ordered_program_append' in Ord as (?& Ord); eauto.
      unfold Ordered_program in Ord; rewrite units_of_update in Ord.
      inversion_clear Ord as [|?? (Spec &?)].
      intro Called; apply Spec in Called as (?&?&?& Find).
      rewrite update_idempotent in Find.
      apply find_unit_In in Find as (?& Hin).
      rewrite units_of_update in Hin.
      apply find_unit_None in Findg.
      rewrite E in Findg.
      apply Forall_app in Findg as (?& Findg).
      apply Forall_cons2 in Findg as (?& Findg).
      eapply Forall_forall with (2 := Hin) in Findg; auto.
    Qed.

  End Ordered.

End Program.

Section Transformation.

  Class TransformUnit (U U': Type) `{ProgramUnit U} `{ProgramUnit U'} :=
    { transform_unit : U -> U';
      transform_unit_conservative_name : forall u, name (transform_unit u) = name u
    }.

  Class TransformStateUnit (U U': Type) {T: Type}
        `{P: ProgramStateUnit U T} `{P': ProgramStateUnit U' T} :=
    { TransformStateUnitTransformUnit :: TransformUnit U U';
      transform_unit_conservative_state :
        forall u, Permutation (state_variables (transform_unit u)) (state_variables u)
             /\ Permutation (instance_variables (transform_unit u)) (instance_variables u)
    }.

  Section Program.

    Class TransformProgramWithoutUnits (Prog Prog' : Type) {U: Type} `{Program U Prog} :=
      { transform_program_without_units : Prog -> Prog';

        transform_program_without_units_update:
          forall p us,
            transform_program_without_units (update p us)
            = transform_program_without_units p
      }.

    Context {U U' Prog Prog': Type}
            `{TransformUnit U U'}
            `{ProgInst: Program U Prog} `{Program U' Prog'}
            `{@TransformProgramWithoutUnits Prog Prog' _ ProgInst}.

    Definition transform_units (p: Prog) : Prog' :=
      update (transform_program_without_units p) (map transform_unit (units p)).

    Lemma find_unit_transform_units_backward:
      forall f p tu tp',
        find_unit f (transform_units p) = Some (tu, tp') ->
        exists u p',
          find_unit f p = Some (u, p')
          /\ tu = transform_unit u
          /\ tp' = transform_units p'.
    Proof.
      unfold find_unit, transform_units; simpl.
      setoid_rewrite units_of_update.
      intros ??; induction (units p) as [|u']; simpl; intros * Find; try discriminate.
      rewrite transform_unit_conservative_name in Find.
      destruct (ident_eq_dec (name u') f).
      - inv Find. do 2 eexists; intuition eauto.
        now rewrite update_idempotent, units_of_update, transform_program_without_units_update.
      - destruct ((fix find (p : list U') : option (U' * list U') :=
                     match p with
                     | [] => None
                     | u :: p0 => if ident_eq_dec (name u) f then Some (u, p0) else find p0
                     end) (map transform_unit l)) as [[]|]; try discriminate.
        rewrite update_idempotent in Find, IHl; auto.
    Qed.

    Lemma find_unit_transform_units_forward:
      forall f p u p',
        find_unit f p = Some (u, p') ->
        find_unit f (transform_units p) = Some (transform_unit u, transform_units p').
    Proof.
      unfold find_unit, transform_units.
      setoid_rewrite units_of_update.
      intros ??; induction (units p) as [|u']; intros * Find;
        simpl; try discriminate.
      rewrite transform_unit_conservative_name.
      destruct (ident_eq_dec (name u') f).
      - inv Find.
        now rewrite update_idempotent, units_of_update, transform_program_without_units_update.
      - apply IHl in Find.
        cases; now rewrite update_idempotent in *.
    Qed.

    Lemma transform_units_Ordered_program:
      forall p (Is_called_in: ident -> U -> Prop) (Is_called_in': ident -> U' -> Prop),
        (forall f u, Is_called_in' f (transform_unit u) -> Is_called_in f u) ->
        Ordered_program Is_called_in p ->
        Ordered_program Is_called_in' (transform_units p).
    Proof.
      unfold Ordered_program, transform_units; intros * SpecCall Ord;
        rewrite units_of_update; induction Ord as [|?? (Spec & Ndp)]; simpl;
          constructor; auto.
      - split.
        + intros * Called; apply SpecCall, Spec in Called as (?&?&?& Find); subst.
          apply find_unit_transform_units_forward in Find.
          unfold transform_units in Find; rewrite transform_program_without_units_update, units_of_update in Find.
          rewrite transform_unit_conservative_name, update_idempotent.
          intuition eauto.
        + apply Forall_map, Forall_forall; intros * Hin.
          eapply Forall_forall in Hin; eauto; simpl in Hin.
          now rewrite 2 transform_unit_conservative_name.
      - eapply Forall'_impl; eauto; simpl; intros * (Spec' &?); split; auto.
        intros * Called; apply Spec' in Called as (?&?&?&Find).
        rewrite update_idempotent in *.
        intuition eauto.
    Qed.

  End Program.

End Transformation.

Global Hint Resolve suffix_refl suffix_cons : program.
Global Hint Resolve find_unit_transform_units_backward find_unit_transform_units_forward
       transform_units_Ordered_program : program.
